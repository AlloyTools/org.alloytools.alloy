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

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents an illegal pred/fun call.
 * <p>
 * <b>Invariant:</b> this.type==EMPTY && this.errors.size()>0
 */

public final class ExprBadCall extends Expr {

    /** The function. */
    public final Func            fun;

    /** The unmodifiable list of arguments. */
    public final ConstList<Expr> args;

    /**
     * The extra weight added to this node on top of the combined weights of the
     * arguments.
     */
    public final long            extraWeight;

    /** Caches the span() result. */
    private Pos                  span = null;

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

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(fun.label).append('[');
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
            out.append("ExprBadCall: ").append(fun.isPred ? "pred " : "fun ").append(fun.label).append('\n');
            for (Expr a : args) {
                a.toString(out, indent + 2);
            }
        }
    }

    /** Constructs an ExprBadCall object. */
    private ExprBadCall(Pos pos, Pos closingBracket, boolean ambiguous, Func fun, ConstList<Expr> args, JoinableList<Err> errors, long extraWeight, long weight) {
        super(pos, closingBracket, ambiguous, EMPTY, 0, weight, errors);
        this.fun = fun;
        this.args = args;
        this.extraWeight = extraWeight;
    }

    /** Constructs an ExprBadCall object. */
    public static Expr make(final Pos pos, final Pos closingBracket, final Func fun, ConstList<Expr> args, long extraPenalty) {
        if (extraPenalty < 0)
            extraPenalty = 0;
        if (args == null)
            args = ConstList.make();
        long weight = extraPenalty;
        boolean ambiguous = false;
        JoinableList<Err> errors = emptyListOfErrors;
        for (Expr x : args) {
            weight = weight + x.weight;
            ambiguous = ambiguous || x.ambiguous;
            errors = errors.make(x.errors);
        }
        if (errors.isEmpty()) {
            StringBuilder sb = new StringBuilder("This cannot be a correct call to ");
            sb.append(fun.isPred ? "pred " : "fun ");
            sb.append(fun.label);
            sb.append(fun.count() == 0 ? ".\nIt has no parameters,\n" : ".\nThe parameters are\n");
            for (ExprVar v : fun.params()) {
                sb.append("  ").append(v.label).append(": ").append(v.type).append('\n');
            }
            sb.append(args.size() == 0 || fun.count() == 0 ? "so the arguments cannot be empty.\n" : "so the arguments cannot be\n");
            int n = fun.count();
            for (Expr v : args) {
                if (n == 0)
                    break;
                else
                    n--;
                sb.append("  ");
                v.toString(sb, -1);
                sb.append(" (type = ").append(v.type).append(")\n");
            }
            errors = errors.make(new ErrorType(pos, sb.toString()));
        }
        return new ExprBadCall(pos, closingBracket, ambiguous, fun, args, errors, extraPenalty, weight);
    }

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
    public Expr resolve(Type t, Collection<ErrorWarning> warns) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>error</b> (parser or typechecker failed)";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return new ArrayList<Browsable>(0);
    }
}
