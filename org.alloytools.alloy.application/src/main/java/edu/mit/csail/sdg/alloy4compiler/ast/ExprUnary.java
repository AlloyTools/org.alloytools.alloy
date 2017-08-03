/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.ast;

import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;
import static edu.mit.csail.sdg.alloy4compiler.ast.Type.EMPTY;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;

import edu.mit.csail.sdg.alloy4.DirectedGraph;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type.ProductType;

/** Immutable; represents a unary expression of the form "(OP subexpression)"
 *
 * <p> <b>Invariant:</b>  type!=EMPTY => sub.mult==0
 */

public final class ExprUnary extends Expr {

    /** The unary operator. */
    public final Op op;

    /** The subexpression. */
    public final Expr sub;

    /** Caches the span() result. */
    private Pos span=null;

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public Pos span() {
        Pos p=span;
        if (p==null) { if (op==Op.NOOP && pos!=Pos.UNKNOWN) span=(p=pos); else span=(p=pos.merge(sub.span())); }
        return p;
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public void toString(StringBuilder out, int indent) {
        if (indent<0) {
            switch(op) {
              case SOMEOF: out.append("some "); break;
              case LONEOF: out.append("lone "); break;
              case ONEOF: out.append("one "); break;
              case SETOF: out.append("set "); break;
              case EXACTLYOF: out.append("exactly "); break;
              case CAST2INT: out.append("int["); sub.toString(out,-1); out.append(']'); return;
              case CAST2SIGINT: out.append("Int["); sub.toString(out,-1); out.append(']'); return;
              case NOOP: break;
              default: out.append(op).append(' ');
            }
            sub.toString(out,-1);
        } else {
            for(int i=0; i<indent; i++) { out.append(' '); }
            out.append(op).append(" with type=").append(type).append('\n');
            sub.toString(out, indent+2);
        }
    }

    //============================================================================================================//

    /** Constructs an unary expression. */
    private ExprUnary(Pos pos, Op op, Expr sub, Type type, long weight, JoinableList<Err> errors) {
        super(pos, null, sub.ambiguous, type, (op==Op.EXACTLYOF||op==Op.SOMEOF||op==Op.LONEOF||op==Op.ONEOF||op==Op.SETOF)?1:0, weight, errors);
        this.op = op;
        this.sub = sub;
    }

    //============================================================================================================//

    /** Returns true if we can determine the two expressions are equivalent; may sometimes return false. */
    @Override public boolean isSame(Expr obj) {
        if (op==Op.NOOP) return sub.isSame(obj);
        while(obj instanceof ExprUnary && ((ExprUnary)obj).op==ExprUnary.Op.NOOP) obj=((ExprUnary)obj).sub;
        if (obj==this) return true;
        if (!(obj instanceof ExprUnary)) return false;
        ExprUnary x=(ExprUnary)obj;
        return op==x.op && sub.isSame(x.sub);
    }

    //============================================================================================================//

    /** This class contains all possible unary operators. */
    public enum Op {
        /** :some     x (where x is a unary set)                         */  SOMEOF("some of"),
        /** :lone     x (where x is a unary set)                         */  LONEOF("lone of"),
        /** :one      x (where x is a unary set)                         */  ONEOF("one of"),
        /** :set      x (where x is a set or relation)                   */  SETOF("set of"),
        /** :exactly  x (where x is a set or relation)                   */  EXACTLYOF("exactly of"),
        /** not   f (where f is a formula)                               */  NOT("!"),
        /** no    x (where x is a set or relation)                       */  NO("no"),
        /** some  x (where x is a set or relation)                       */  SOME("some"),
        /** lone  x (where x is a set or relation)                       */  LONE("lone"),
        /** one   x (where x is a set or relation)                       */  ONE("one"),
        /** transpose                                                    */  TRANSPOSE("~"),
        /** reflexive closure                                            */  RCLOSURE("*"),
        /** closure                                                      */  CLOSURE("^"),
        /** cardinality of x (truncated to the current integer bitwidth) */  CARDINALITY("#"),
        /** IntAtom-to-integer                                           */  CAST2INT("Int->int"),
        /** integer-to-IntAtom                                           */  CAST2SIGINT("int->Int"),
        /** No-Operation                                                 */  NOOP("NOOP");

        /** The constructor */
        private Op(String label) {this.label=label;}

        /** The human readable label for this operator */
        private final String label;

        /** Construct an ExprUnary node.
         * @param pos - the original position of the "unary operator" in the file (can be null if unknown)
         * @param sub - the subexpression
         *
         * <p>  Alloy4 disallows multiplicity like this:   "variable : one (X lone-> Y)",
         * <br> that is, a some/lone/one in front of an arrow multiplicity declaration.
         * <br> Alloy4 does allow "variable : set (X lone-> Y)", where we ignore the word "set".
         * <br> (This desugaring is done by the ExprUnary.Op.make() method, so ExprUnary's constructor never sees it)
         */
        public final Expr make(Pos pos, Expr sub) { return make(pos, sub, null, 0); }

        /** Construct an ExprUnary node.
         * @param pos - the original position of the "unary operator" in the file (can be null if unknown)
         * @param sub - the subexpression
         * @param extraError - if nonnull, it will be appended as an extra error
         * @param extraWeight - it's the amount of extra weight
         *
         * <p>  Alloy4 disallows multiplicity like this:   "variable : one (X lone-> Y)",
         * <br> that is, a some/lone/one in front of an arrow multiplicity declaration.
         * <br> Alloy4 does allow "variable : set (X lone-> Y)", where we ignore the word "set".
         * <br> (This desugaring is done by the ExprUnary.Op.make() method, so ExprUnary's constructor never sees it)
         */
        public final Expr make(Pos pos, Expr sub, Err extraError, long extraWeight) {
            if (pos==null || pos==Pos.UNKNOWN) { if (this==NOOP) pos = sub.pos; else pos = sub.span(); }
            JoinableList<Err> errors = sub.errors.make(extraError);
            if (sub.mult!=0) {
               if (this==SETOF) return sub;
               if (this!=NOOP && extraError==null)
                  errors = errors.make(new ErrorSyntax(sub.span(), "Multiplicity expression not allowed here."));
               // When you have a multiplicity expression like (A one->one B), and you call cint() on it,
               // cint() will try to compose a NOOP node around the (A one->one B) with the error message "This must be an integer!"
               // So in such a case, we will have a "NOOP" in front of a "MULTIPLICITY", and we don't want
               // to clutter the output window with an extra useless report of "Multiplicity expression not allowed here!"
            }
            extraError=null;
            switch(this) {
               case NOOP: break;
               case NOT: sub=sub.typecheck_as_formula(); break;
               case CAST2SIGINT: 
                   if (sub instanceof ExprUnary)
                       if (((ExprUnary) sub).op == CAST2SIGINT)
                           return sub;
                   sub=sub.typecheck_as_int(); 
                   break;
               case CAST2INT: 
                   if (sub instanceof ExprUnary) {
                       // shortcircuit
                       ExprUnary sub2 = (ExprUnary) sub;
                       if (sub2.op == CAST2INT)
                           return sub2;
                       if (sub2.op == CAST2SIGINT)
                           return sub2.sub;
                   }
                   sub=sub.typecheck_as_set(); 
                   break;
               default: sub=sub.typecheck_as_set();
            }
            Type type=sub.type;
            if (sub.errors.isEmpty()) switch(this) {
              case EXACTLYOF: case SOMEOF: case LONEOF: case ONEOF: case SETOF:
                if (this==SETOF || this==EXACTLYOF) type=Type.removesBoolAndInt(sub.type); else type=sub.type.extract(1);
                if (type==EMPTY) extraError=new ErrorType(sub.span(), "After the some/lone/one multiplicity symbol, " +
                   "this expression must be a unary set.\nInstead, its possible type(s) are:\n" + sub.type);
                break;
              case NOT: case NO: case SOME: case LONE: case ONE:
                type=Type.FORMULA;
                break;
              case TRANSPOSE:
                type=sub.type.transpose();
                if (type==EMPTY) extraError=new ErrorType(sub.span(), "~ can be used only with a binary relation.\n" +
                   "Instead, its possible type(s) are:\n"+sub.type);
                break;
              case RCLOSURE: case CLOSURE:
                type=sub.type.closure();
                if (type==EMPTY) extraError=new ErrorType(sub.span(), label+" can be used only with a binary relation.\n" +
                   "Instead, its possible type(s) are:\n"+sub.type);
                if (this==RCLOSURE) type=Type.make2(UNIV);
                break;
              case CARDINALITY:
                type=Type.smallIntType();
                break;
              case CAST2INT:
                if (!sub.type.hasArity(1)) extraError=new ErrorType(sub.span(), "int[] can be used only with a unary set.\n" +
                   "Instead, its possible type(s) are:\n"+sub.type);
                type=Type.smallIntType();
                break;
              case CAST2SIGINT:
                type=SIGINT.type;
                break;
            }
            return new ExprUnary(pos, this, sub, type, extraWeight + sub.weight, errors.make(extraError));
        }

        /** Returns the human readable label for this operator */
        @Override public final String toString() { return label; }

        /** Returns the human readable label already encoded for HTML */
        public final String toHTML() {
            if (this == CAST2INT) return "Int-&gt;int";
            if (this == CAST2SIGINT) return "int-&gt;Int";
            return label;
        }
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public Expr resolve(Type p, Collection<ErrorWarning> warns) {
        if (errors.size()>0) return this;
        ErrorWarning w1=null, w2=null;
        Type s=p;
        switch(op) {
          case NOT:
            s=Type.FORMULA;
            break;
          case TRANSPOSE: case RCLOSURE: case CLOSURE:
            if (warns!=null && op!=Op.TRANSPOSE && type.join(type).hasNoTuple())
               w1=new ErrorWarning(pos, this+" is redundant since its domain and range are disjoint: "+sub.type.extract(2));
            s = (op!=Op.TRANSPOSE) ? resolveClosure(p, sub.type) : sub.type.transpose().intersect(p).transpose() ;
            if (warns!=null && s==EMPTY && p.hasTuple())
               w2=new ErrorWarning(sub.span(),
               "The value of this expression does not contribute to the value of the parent.\nParent's relevant type = "
               +p+"\nThis expression's type = "+sub.type.extract(2));
            break;
          case CARDINALITY: case NO: case ONE: case SOME: case LONE:
            s=Type.removesBoolAndInt(sub.type);
            break;
          case CAST2SIGINT:
            s=Type.smallIntType();
            break;
          case CAST2INT:
            s=sub.type.intersect(SIGINT.type);
            if (warns!=null && s.hasNoTuple())
               w1=new ErrorWarning(sub.span(),
               "This expression should contain Int atoms.\nInstead, its possible type(s) are:\n"+sub.type.extract(1));
            break;
        }
        Expr sub = this.sub.resolve(s, warns);
        if (w1!=null) warns.add(w1);
        if (w2!=null) warns.add(w2);
        return (sub==this.sub) ? this : op.make(pos, sub, null, weight-(this.sub.weight));
    }

    //============================================================================================================//

    /** Helper method that computes the relevant type for a closure expression.
     *
     * <p> Return Value == { c1->c2 | c1->c2 in childType, AND exists p1->p2 in parentType
     *                       where p1..c1..c2..p2 is a path in the closure graph }
     *
     * <p>
     * We need to do this because of situations like this follow:
     * Suppose e's type is "A->B + B->C".
     * Therefore, ^e = A->B + B->C + A->C which makes sense.
     * But as we compute the relevance type back down, we may have lost some entries,
     * and possibly end up with only A->B + A->C so we need to rediscover the relevant edges.
     */
    private static Type resolveClosure (Type parent, Type child) {
        LinkedHashSet<PrimSig> nodes = new LinkedHashSet<PrimSig>();
        DirectedGraph<PrimSig> graph = new DirectedGraph<PrimSig>();
        // For each (v1->v2) in childType, add (v1->v2) into the graph.
        for (ProductType c:child) if (c.arity()==2) {
            PrimSig a=c.get(0), b=c.get(1);
            nodes.add(a);
            nodes.add(b);
            graph.addEdge(a,b);
        }
        // For each distinct v1 and v2 in the graph where v1&v2!=empty, add the edges v1->v2 and v2->v1.
        for (PrimSig a:nodes) for (PrimSig b:nodes) if (a!=b && a.intersects(b)) graph.addEdge(a,b);
        // For each a->b in ParentType:
        // 1) add a
        // 2) add b
        // 3) if a has subtypes/supertypes in the graph, connect between a and them.
        // 4) if b has subtypes/supertypes in the graph, connect between b and them.
        for (ProductType p:parent) if (p.arity()==2) {
            PrimSig a=p.get(0), b=p.get(1);
            // Add edges between a and all its subtypes and supertypes
            if (!nodes.contains(a)) {
                for (PrimSig x:nodes) if (a.intersects(x)) { graph.addEdge(a,x); graph.addEdge(x,a); }
                nodes.add(a);
            }
            // Add edges between b and all its subtypes and supertypes
            if (!nodes.contains(b)) {
                for (PrimSig x:nodes) if (b.intersects(x)) { graph.addEdge(b,x); graph.addEdge(x,b); }
                nodes.add(b);
            }
        }
        // For each c1->c2 in childType, add c1->c2 into the finalType if there exists p1->p2 in parentType
        // such that p1->..->c1->c2->..->p2 is a path in the graph.
        Type answer=Type.EMPTY;
        for (ProductType c:child) if (c.arity()==2) {
            PrimSig c1=c.get(0), c2=c.get(1);
            for (ProductType p:parent) if (p.arity()==2) {
                PrimSig p1=p.get(0), p2=p.get(1);
                if (graph.hasPath(p1,c1) && graph.hasPath(c2,p2)) { answer=answer.merge(c); break; }
            }
        }
        return answer;
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    public int getDepth() { return 1 + sub.getDepth(); }

    /** {@inheritDoc} */
    @Override public final<T> T accept(VisitReturn<T> visitor) throws Err { return visitor.visit(this); }

    /** {@inheritDoc} */
    @Override public String getHTML() { return op==Op.NOOP ? sub.getHTML() : (op+" <i>" + type + "</i>"); }

    /** {@inheritDoc} */
    @Override public List<? extends Browsable> getSubnodes() { return op==Op.NOOP ? sub.getSubnodes() : Util.asList(sub); }
}
