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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents a quantified expression. It can have one of the
 * following forms: <br>
 * <br>
 * ( all a,b:t | formula ) <br>
 * ( no a,b:t | formula ) <br>
 * ( lone a,b:t | formula ) <br>
 * ( one a,b:t | formula ) <br>
 * ( some a,b:t | formula ) <br>
 * ( sum a,b:t | integer expression ) <br>
 * { a,b:t | formula } <br>
 * { a,b:t } <br>
 * <br>
 * <b>Invariant:</b> type!=EMPTY => sub.mult==0 <br>
 * <b>Invariant:</b> type!=EMPTY => vars.size()>0
 */

public final class ExprQt extends Expr {

    /**
     * The operator (ALL, NO, LONE, ONE, SOME, SUM, or COMPREHENSION)
     */
    public final Op              op;

    /** The unmodifiable list of variables. */
    public final ConstList<Decl> decls;

    /** The body of the quantified expression. */
    public final Expr            sub;

    /** Caches the span() result. */
    private Pos                  span;

    /** Return the number of variables. */
    public int count() {
        int n = 0;
        for (Decl d : decls)
            n = n + d.names.size();
        return n;
    }

    /** Return the i-th variable. */
    public ExprVar get(int i) {
        if (i < 0)
            throw new NoSuchElementException();
        for (Decl d : decls) {
            if (i < d.names.size())
                return (ExprVar) (d.names.get(i));
            i = i - d.names.size();
        }
        throw new NoSuchElementException();
    }

    /** Return the i-th variable's bound. */
    public Expr getBound(int i) {
        if (i < 0)
            throw new NoSuchElementException();
        for (Decl d : decls) {
            if (i < d.names.size())
                return d.expr;
            i = i - d.names.size();
        }
        throw new NoSuchElementException();
    }

    // =============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        // We intentionally do NOT merge the VAR's position into the span.
        // That allows us to control the highlighting of this component
        // simply by deciding this.pos and this.closingBracket
        if (p == null)
            span = (p = pos.merge(closingBracket).merge(sub.span()));
        return p;
    }

    // =============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            boolean first = true;
            if (op != Op.COMPREHENSION)
                out.append('(').append(op).append(' ');
            else
                out.append('{');
            for (Decl d : decls)
                for (ExprHasName v : d.names) {
                    if (!first)
                        out.append(',');
                    first = false;
                    out.append(v.label);
                }
            if (op != Op.COMPREHENSION || !(sub instanceof ExprConstant) || ((ExprConstant) sub).op != ExprConstant.Op.TRUE) {
                out.append(" | ");
                sub.toString(out, -1);
            }
            if (op != Op.COMPREHENSION)
                out.append(')');
            else
                out.append('}');
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("Quantification(").append(op).append(") of ");
            out.append(count()).append(" vars with type=").append(type).append('\n');
            for (Decl d : decls)
                for (ExprHasName v : d.names) {
                    v.toString(out, indent + 2);
                    d.expr.toString(out, indent + 4);
                }
            sub.toString(out, indent + 2);
        }
    }

    // =============================================================================================================//

    /** Constructs a new quantified expression. */
    private ExprQt(Pos pos, Pos closingBracket, Op op, Type type, ConstList<Decl> decls, Expr sub, boolean ambiguous, long weight, JoinableList<Err> errs) {
        super(pos, closingBracket, ambiguous, type, 0, weight, errs);
        this.op = op;
        this.decls = decls;
        this.sub = sub;
    }

    // =============================================================================================================//

    /**
     * This class contains all possible quantification operators.
     */
    public enum Op {
                    /** all a,b:x | formula */
                    ALL("all"),
                    /** no a,b:x | formula */
                    NO("no"),
                    /** lone a,b:x | formula */
                    LONE("lone"),
                    /** one a,b:x | formula */
                    ONE("one"),
                    /** some a,b:x | formula */
                    SOME("some"),
                    /** sum a,b:x | intExpression */
                    SUM("sum"),
                    /** { a,b:x | formula } */
                    COMPREHENSION("comprehension");

        /** The constructor. */
        private Op(String label) {
            this.label = label;
        }

        /** The human readable label for this operator. */
        private final String label;

        /**
         * Constructs a quantification expression with "this" as the operator.
         *
         * @param pos - the position of the "quantifier" in the source file (or null if
         *            unknown)
         * @param closingBracket - the position of the "closing bracket" in the source
         *            file (or null if unknown)
         * @param decls - the list of variable declarations (each variable must be over
         *            a set or relation)
         * @param sub - the body of the expression
         */
        public final Expr make(Pos pos, Pos closingBracket, List<Decl> decls, Expr sub) {
            Type t = this == SUM ? Type.smallIntType() : (this == COMPREHENSION ? Type.EMPTY : Type.FORMULA);
            if (this != SUM)
                sub = sub.typecheck_as_formula();
            else
                sub = sub.typecheck_as_int();
            boolean ambiguous = sub.ambiguous;
            JoinableList<Err> errs = emptyListOfErrors;
            if (sub.mult != 0)
                errs = errs.make(new ErrorSyntax(sub.span(), "Multiplicity expression not allowed here."));
            long weight = sub.weight;
            if (decls.size() == 0)
                errs = errs.make(new ErrorSyntax(pos, "List of variables cannot be empty."));
            for (Decl d : decls) {
                Expr v = d.expr;
                ambiguous = ambiguous || v.ambiguous;
                weight = weight + v.weight;
                errs = errs.make(v.errors);
                if (v.errors.size() > 0)
                    continue;
                if (v.type.size() == 0) {
                    errs = errs.make(new ErrorType(v.span(), "This must be a set or relation. Instead, its type is " + v.type));
                    continue;
                }
                ExprUnary.Op op = v.mult();
                if (op == ExprUnary.Op.EXACTLYOF) {
                    errs = errs.make(new ErrorType(v.span(), "This cannot be an exactly-of expression."));
                    continue;
                }
                if (this != SUM && this != COMPREHENSION)
                    continue;
                if (!v.type.hasArity(1)) {
                    errs = errs.make(new ErrorType(v.span(), "This must be a unary set. Instead, its type is " + v.type));
                    continue;
                }
                if (v.mult == 1) {
                    if (op == ExprUnary.Op.SETOF)
                        errs = errs.make(new ErrorType(v.span(), "This cannot be a set-of expression."));
                    else if (op == ExprUnary.Op.SOMEOF)
                        errs = errs.make(new ErrorType(v.span(), "This cannot be a some-of expression."));
                    else if (op == ExprUnary.Op.LONEOF)
                        errs = errs.make(new ErrorType(v.span(), "This cannot be a lone-of expression."));
                }
                if (this == COMPREHENSION) {
                    Type t1 = v.type.extract(1);
                    for (int n = d.names.size(); n > 0; n--)
                        if (t == EMPTY)
                            t = t1;
                        else
                            t = t.product(t1);
                }
            }
            if (errs.isEmpty())
                errs = sub.errors; // if the vars have errors, then the
                                  // subexpression's errors will be too
                                  // confusing, so let's skip them
            return new ExprQt(pos, closingBracket, this, t, ConstList.make(decls), sub, ambiguous, weight, errs);
        }

        /** Returns the human readable label for this operator */
        @Override
        public final String toString() {
            return label;
        }
    }

    // =============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type unused, Collection<ErrorWarning> warns) {
        if (warns != null && op != Op.COMPREHENSION) {
            for (int i = 0; i < decls.size(); i++) {
                again: for (ExprHasName n : decls.get(i).names) {
                    ExprVar x = (ExprVar) n;
                    for (int j = i + 1; j < decls.size(); j++)
                        if (decls.get(j).expr.hasVar(x))
                            continue again;
                    if (!sub.hasVar(x))
                        warns.add(new ErrorWarning(x.pos, "This variable is unused."));
                }
            }
        }
        return this;
    }

    // =============================================================================================================//

    /**
     * This method desugars away the "disjoint" keyword by prefixing the
     * subexpression with the appropriate disjointness guard condition.
     */
    public Expr desugar() throws ErrorSyntax {
        boolean hasDisjoint = false;
        for (Decl d : decls) {
            if (d.isPrivate != null) {
                ExprHasName n = d.names.get(0);
                throw new ErrorSyntax(d.isPrivate.merge(n.pos), "Local variable \"" + n.label + "\" is always private already.");
            }
            if (d.disjoint2 != null) {
                ExprHasName n = d.names.get(d.names.size() - 1);
                throw new ErrorSyntax(d.disjoint2.merge(n.pos), "Local variable \"" + n.label + "\" cannot be bound to a 'disjoint' expression.");
            }
            hasDisjoint = hasDisjoint || (d.names.size() > 1 && d.disjoint != null);
        }
        if (!hasDisjoint)
            return this;
        TempList<Decl> newdecls = new TempList<Decl>(decls.size());
        Expr guard = null;
        for (Decl d : decls) {
            if (d.names.size() <= 1 || d.disjoint == null) {
                newdecls.add(d);
                continue;
            }
            guard = ExprList.makeDISJOINT(d.disjoint, null, d.names).and(guard);
            newdecls.add(new Decl(null, null, null, d.names, d.expr));
        }
        if (guard == null)
            return this;
        Expr sub;
        switch (op) {
            case SUM :
                sub = guard.ite(this.sub, ExprConstant.ZERO);
                break;
            case ALL :
                sub = guard.implies(this.sub);
                break;
            default :
                sub = guard.and(this.sub);
        }
        return op.make(pos, closingBracket, newdecls.makeConst(), sub);
    }

    // =============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = sub.getDepth();
        for (Decl d : decls)
            for (ExprHasName x : d.names) {
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
        StringBuilder sb = new StringBuilder("<b>").append(op).append("</b> ");
        boolean first = true;
        for (Decl d : decls)
            for (ExprHasName v : d.names) {
                if (!first)
                    sb.append(", ");
                sb.append(v.label);
                first = false;
            }
        return sb.append("... <i>").append(type).append("</i>").toString();
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        ArrayList<Browsable> ans = new ArrayList<Browsable>();
        for (Decl d : decls)
            for (ExprHasName v : d.names) {
                ans.add(make(v.pos, v.pos, "<b>var</b> " + v.label + " <i>" + v.type + "</i>", d.expr));
            }
        ans.add(make(sub.span(), sub.span(), "<b>body</b>", sub));
        return ans;
    }
}
