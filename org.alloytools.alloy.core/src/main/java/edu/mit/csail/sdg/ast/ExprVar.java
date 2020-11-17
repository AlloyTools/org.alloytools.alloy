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

import static edu.mit.csail.sdg.alloy4.TableView.clean;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents a LET or QUANTIFICATION variable in the AST.
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (type==expr.type && !expr.ambiguous)
 */

public final class ExprVar extends ExprHasName implements Clause {

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("Var ").append(label).append(" at position <").append(pos).append("> with type=").append(type).append('\n');
        }
    }

    /** Constructs an ExprVar object */
    private ExprVar(Pos pos, String label, Type type) {
        super(pos, label, type);
    }

    /**
     * Constructs an ExprVar variable with the EMPTY type
     *
     * @param pos - the original position in the source file (can be null if
     *            unknown)
     * @param label - the label for this variable (it is only used for
     *            pretty-printing and does not have to be unique)
     */
    public static ExprVar make(Pos pos, String label) {
        return new ExprVar(pos, label, Type.EMPTY);
    }

    /**
     * Constructs an ExprVar variable with the given type
     *
     * @param pos - the original position in the source file (can be null if
     *            unknown)
     * @param label - the label for this variable (it is only used for
     *            pretty-printing and does not have to be unique)
     * @param type - the type
     */
    public static ExprVar make(Pos pos, String label, Type type) {
        return new ExprVar(pos, label, type);
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type p, Collection<ErrorWarning> warns) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>variable</b>: " + label + " <i>" + type + "</i>";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return new ArrayList<Browsable>(0);
    }

    @Override
    public String explain() {
        return clean(type.explain()) + " : " + label;
    }
}
