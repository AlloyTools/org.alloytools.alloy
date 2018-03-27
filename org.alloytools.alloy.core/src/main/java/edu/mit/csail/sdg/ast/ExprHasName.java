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

import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents a named entity (such as a Field, or a LET or
 * QUANTIFICATION variable, or a function/predicate parameter).
 */

public abstract class ExprHasName extends Expr {

    /**
     * The label associated with this object; it's used for pretty-printing and does
     * not have to be unique.
     */
    public final String label;

    /** Constructs an ExprHasName object */
    ExprHasName(Pos pos, String label, Type type) {
        super(pos, null, false, type, 0, 0, null);
        this.label = (label == null ? "" : label);
    }

    /** {@inheritDoc} */
    @Override
    public final boolean isSame(Expr obj) {
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        return this == obj;
    }

    /** {@inheritDoc} */
    @Override
    public final Pos span() {
        return pos;
    }

    /** {@inheritDoc} */
    @Override
    public final int getDepth() {
        return 1;
    }
}
