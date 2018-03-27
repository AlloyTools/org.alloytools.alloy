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

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.ast.Type.EMPTY;

import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Sig.Field;

/**
 * Immutable; represents a call.
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (all x:args | x.mult==0)
 */

public final class ExprCall extends Expr {

    /** The actual function being called; never null. */
    public final Func            fun;

    /** The list of arguments to the call. */
    public final ConstList<Expr> args;

    /**
     * The extra weight added to this node on top of the combined weights of the
     * arguments.
     */
    public final long            extraWeight;

    /** Caches the span() result. */
    private Pos                  span = null;

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        if (p == null) {
            p = pos.merge(closingBracket);
            for (Expr a : args)
                p = p.merge(a.span());
            span = p;
        }
        return p;
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(fun.label);
            if (args.size() == 0)
                return;
            out.append('[');
            for (int i = 0; i < args.size(); i++) {
                if (i > 0)
                    out.append(", ");
                args.get(i).toString(out, -1);
            }
            out.append(']');
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("call ").append(fun).append(" at position <").append(fun.pos).append("> with type=").append(type).append('\n');
            for (Expr a : args) {
                a.toString(out, indent + 2);
            }
        }
    }

    // ============================================================================================================//

    /**
     * This visitor assumes the input expression is already fully typechecked, and
     * derive a tight bound on the return type.
     */
    private static final class DeduceType extends VisitReturn<Type> {

        private final Env<ExprVar,Type> env = new Env<ExprVar,Type>();

        private DeduceType() {}

        @Override
        public Type visit(ExprITE x) throws Err {
            Type t = x.left.accept(this);
            if (t.size() == 0)
                return t;
            Type t2 = x.right.accept(this);
            return t.unionWithCommonArity(t2);
        }

        @Override
        public Type visit(ExprBinary x) throws Err {
            switch (x.op) {
                case IMPLIES :
                case GT :
                case GTE :
                case LT :
                case LTE :
                case IFF :
                case EQUALS :
                case IN :
                case OR :
                case AND :
                case NOT_LT :
                case NOT_GT :
                case NOT_LTE :
                case NOT_GTE :
                case NOT_IN :
                case NOT_EQUALS :
                    return Type.FORMULA;
                case MUL :
                case DIV :
                case REM :
                case SHL :
                case SHR :
                case SHA :
                    return Type.smallIntType();
            }
            Type a = x.left.accept(this);
            Type b = x.right.accept(this);
            switch (x.op) {
                case JOIN :
                    return a.join(b);
                case DOMAIN :
                    return b.domainRestrict(a);
                case RANGE :
                    return a.rangeRestrict(b);
                case INTERSECT :
                    return a.intersect(b);
                case PLUSPLUS :
                    return a.unionWithCommonArity(b);
                case PLUS :
                    return a.unionWithCommonArity(b); // [AM]: return
                                                     // (a.is_int() &&
                                                     // b.is_int()) ?
                                                     // Type.makeInt(a.unionWithCommonArity(b))
                                                     // :
                                                     // a.unionWithCommonArity(b);
                case IPLUS :
                case IMINUS :
                    return Type.smallIntType();
                case MINUS :
                    return a.pickCommonArity(b); // [AM]: return (a.is_int() &&
                                                // b.is_int()) ?
                                                // Type.makeInt(a.pickCommonArity(b))
                                                // : a.pickCommonArity(b);
                default :
                    return a.product(b);
            }
        }

        @Override
        public Type visit(ExprUnary x) throws Err {
            Type t = x.sub.accept(this);
            switch (x.op) {
                case NOOP :
                case LONEOF :
                case ONEOF :
                case SETOF :
                case SOMEOF :
                case EXACTLYOF :
                    return t;
                case CARDINALITY :
                case CAST2INT :
                    return Type.smallIntType();
                case CAST2SIGINT :
                    return Sig.SIGINT.type;
                case TRANSPOSE :
                    return t.transpose();
                case CLOSURE :
                    return t.closure();
                case RCLOSURE :
                    return Type.make2(Sig.UNIV);
                default :
                    return Type.FORMULA;
            }
        }

        @Override
        public Type visit(ExprQt x) throws Err {
            if (x.op == ExprQt.Op.SUM)
                return Type.smallIntType();
            if (x.op != ExprQt.Op.COMPREHENSION)
                return Type.FORMULA;
            Type ans = null;
            for (Decl d : x.decls) {
                Type t = d.expr.accept(this);
                for (ExprHasName v : d.names) {
                    env.put((ExprVar) v, t);
                    if (ans == null)
                        ans = t;
                    else
                        ans = ans.product(t);
                }
            }
            for (Decl d : x.decls)
                for (ExprHasName v : d.names)
                    env.remove((ExprVar) v);
            return (ans == null) ? EMPTY : ans;
        }

        @Override
        public Type visit(ExprLet x) throws Err {
            env.put(x.var, x.expr.accept(this));
            Type ans = x.sub.accept(this);
            env.remove(x.var);
            return ans;
        }

        @Override
        public Type visit(ExprCall x) throws Err {
            throw new ErrorSyntax(x.span(), "Return type declaration cannot contain predicate/function calls.");
        }

        @Override
        public Type visit(ExprVar x) {
            Type t = env.get(x);
            return (t != null && t != EMPTY) ? t : x.type;
        }

        @Override
        public Type visit(ExprConstant x) {
            return x.type;
        }

        @Override
        public Type visit(Sig x) {
            return x.type;
        }

        @Override
        public Type visit(Field x) {
            return x.type;
        }

        @Override
        public Type visit(ExprList x) {
            return Type.FORMULA;
        }
    }

    // ============================================================================================================//

    /**
     * Constructs an ExprCall node with the given function "pred/fun" and the list
     * of arguments "args".
     */
    private ExprCall(Pos pos, Pos closingBracket, boolean ambiguous, Type type, Func fun, ConstList<Expr> args, long extraWeight, long weight, JoinableList<Err> errs) {
        super(pos, closingBracket, ambiguous, type, 0, weight, errs);
        this.fun = fun;
        this.args = args;
        this.extraWeight = extraWeight;
    }

    // ============================================================================================================//

    /**
     * Returns true if we can determine the two expressions are equivalent; may
     * sometimes return false.
     */
    @Override
    public boolean isSame(Expr obj) {
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        if (obj == this)
            return true;
        if (!(obj instanceof ExprCall))
            return false;
        ExprCall x = (ExprCall) obj;
        if (fun != x.fun || args.size() != x.args.size())
            return false;
        for (int i = 0; i < args.size(); i++)
            if (!args.get(i).isSame(x.args.get(i)))
                return false;
        return true;
    }

    // ============================================================================================================//

    /**
     * Constructs an ExprCall node with the given predicate/function "fun" and the
     * list of arguments "args".
     */
    public static Expr make(Pos pos, Pos closingBracket, Func fun, List<Expr> args, long extraPenalty) {
        if (extraPenalty < 0)
            extraPenalty = 0;
        if (args == null)
            args = ConstList.make();
        long weight = extraPenalty;
        boolean ambiguous = false;
        JoinableList<Err> errs = emptyListOfErrors;
        TempList<Expr> newargs = new TempList<Expr>(args.size());
        if (args.size() != fun.count()) {
            errs = errs.make(new ErrorSyntax(pos, "" + fun + " has " + fun.count() + " parameters but is called with " + args.size() + " arguments."));
        }
        for (int i = 0; i < args.size(); i++) {
            final int a = (i < fun.count()) ? fun.get(i).type.arity() : 0;
            final Expr x = args.get(i).typecheck_as_set();
            ambiguous = ambiguous || x.ambiguous;
            errs = errs.make(x.errors);
            weight = weight + x.weight;
            if (x.mult != 0)
                errs = errs.make(new ErrorSyntax(x.span(), "Multiplicity expression not allowed here."));
            if (a > 0 && x.errors.isEmpty() && !x.type.hasArity(a))
                errs = errs.make(new ErrorType(x.span(), "This should have arity " + a + " but instead its possible type(s) are " + x.type));
            newargs.add(x);
        }
        Type t = Type.FORMULA;
        if (!fun.isPred && errs.size() == 0) {
            final Type tt = fun.returnDecl.type;
            try {
                // This provides a limited form of polymorphic function,
                // by using actual arguments at each call site to derive a
                // tighter bound on the return value.
                DeduceType d = new DeduceType();
                for (int i = 0; i < args.size(); i++) {
                    ExprVar param = fun.get(i);
                    d.env.put(param, newargs.get(i).type.extract(param.type.arity()));
                }
                t = fun.returnDecl.accept(d);
                if (t == null || t.is_int() || t.is_bool || t.arity() != tt.arity())
                    t = tt; // Just in case an error occurred...
            } catch (Throwable ex) {
                t = tt; // Just in case an error occurred...
            }
        }
        return new ExprCall(pos, closingBracket, ambiguous, t, fun, newargs.makeConst(), extraPenalty, weight, errs);
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warns) {
        if (errors.size() > 0)
            return this;
        TempList<Expr> args = new TempList<Expr>(this.args.size());
        boolean changed = false;
        for (int i = 0; i < this.args.size(); i++) {
            Type p = fun.get(i).type;
            Expr x = this.args.get(i);
            Expr y = x.resolve(p, warns).typecheck_as_set(); // Use the
                                                            // function's
                                                            // param type to
                                                            // narrow down
                                                            // the choices
            if (x != y)
                changed = true;
            args.add(y);
            // if (warns!=null && Version.experimental &&
            // !y.type.isSubtypeOf(p))
            // warns.add(new ErrorWarning(x.span(), "This argument may contain a
            // tuple not in the parameter's type.\n"
            // +"The Alloy Analyzer's analysis may be unsound\n"
            // +"if the argument has a tuple outside the parameter's type.\n"
            // +"The argument has type "+y.type+"\nbut the parameter has type
            // "+p));
        }
        return changed ? make(pos, closingBracket, fun, args.makeConst(), extraWeight) : this;
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = 1;
        for (Expr x : args) {
            int tmp = x.getDepth();
            if (max < tmp)
                max = tmp;
        }
        return 1 + max;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>call</b> " + fun.label + " <i>" + type + "</i>";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        if (args.size() == 0) {
            Expr b = fun.getBody();
            return Util.asList(make(b.pos(), b.span(), b.getHTML(), b.getSubnodes()));
        }
        Pos p = pos;
        if (p == Pos.UNKNOWN)
            p = span();
        Browsable f = make(p, p, (fun.isPred ? "<b>pred</b> " : "<b>fun</b> ") + fun.label, fun.getSubnodes());
        Browsable a = make(span(), span(), "<b>" + args.size() + " argument" + (args.size() == 1 ? "</b>" : "s</b>"), args);
        return Util.asList(f, a);
    }

    @Override
    public Clause referenced() {
        return super.referenced(fun);
    }
}
