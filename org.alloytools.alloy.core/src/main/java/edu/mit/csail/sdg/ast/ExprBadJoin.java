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

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents an illegal relation join.
 * <p>
 * <b>Invariant:</b> this.type==EMPTY && this.errors.size()>0
 */

public final class ExprBadJoin extends Expr {

    /** The left-hand-side expression. */
    public final Expr left;

    /** The right-hand-side expression. */
    public final Expr right;

    /** Caches the span() result. */
    private Pos       span = null;

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        if (p == null)
            span = (p = pos.merge(closingBracket).merge(right.span()).merge(left.span()));
        return p;
    }

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            left.toString(out, -1);
            out.append('.');
            right.toString(out, -1);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("ExprBadJoin:\n");
            left.toString(out, indent + 2);
            right.toString(out, indent + 2);
        }
    }

    /** Constructs an ExprBadJoin node. */
    private ExprBadJoin(Pos pos, Pos closingBracket, Expr left, Expr right, JoinableList<Err> errors) {
        super(pos, closingBracket, (left.ambiguous || right.ambiguous), EMPTY, 0, 0, errors);
        this.left = left;
        this.right = right;
    }

    /** Constructs an ExprBadJoin node. */
    public static Expr make(Pos pos, Pos closingBracket, Expr left, Expr right) {
        JoinableList<Err> errors = left.errors.make(right.errors);
        if (errors.isEmpty()) {
            StringBuilder sb = new StringBuilder("This cannot be a legal relational join where\nleft hand side is ");
            left.toString(sb, -1);
            sb.append(" (type = ").append(left.type).append(")\nright hand side is ");
            right.toString(sb, -1);
            sb.append(" (type = ").append(right.type).append(")\n");
            errors = errors.make(new ErrorType(pos, sb.toString()));
        }
        return new ExprBadJoin(pos, closingBracket, left, right, errors);
    }

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int a = left.getDepth(), b = right.getDepth();
        if (a >= b)
            return 1 + a;
        else
            return 1 + b;
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
