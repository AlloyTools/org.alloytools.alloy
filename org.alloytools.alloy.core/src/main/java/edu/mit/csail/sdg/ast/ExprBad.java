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
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents an illegal node.
 * <p>
 * <b>Invariant:</b> this.type==EMPTY && this.errors.size()==1
 */

public final class ExprBad extends Expr {

    /** The original source text that caused the error. */
    private final String originalText;

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        return pos;
    }

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(originalText);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("ExprBad: ").append(originalText).append('\n');
        }
    }

    /** Constructs an ExprBad object. */
    public ExprBad(Pos pos, String originalText, Err error) {
        super(pos, null, false, EMPTY, 0, 0, new JoinableList<Err>(error));
        this.originalText = originalText;
    }

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        return 1;
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
