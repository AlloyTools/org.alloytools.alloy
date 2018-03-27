/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.ast;

import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * A multiplicity formula, e.g. some x
 *
 * @specfield expression: Expression
 * @specfield multiplicity: (ONE + LONE + SOME + NO)
 * @invariant children = 0->expression
 * @author Emina Torlak
 */
public final class MultiplicityFormula extends Formula {

    private final Expression   expression;
    private final Multiplicity multiplicity;

    /**
     * Constructs a new multiplicity formula: multiplicity expression
     *
     * @ensures this.expression' = expression && this.multiplicity' = multiplicity
     * @throws NullPointerException multiplicity = null || expression = null
     * @throws IllegalArgumentException multiplicity = SET
     */
    MultiplicityFormula(Multiplicity multiplicity, Expression expression) {
        if (multiplicity == Multiplicity.SET)
            throw new IllegalArgumentException("invalid expression mulitplicity: SET");
        if (multiplicity == null || expression == null)
            throw new NullPointerException("null arg");
        this.multiplicity = multiplicity;
        this.expression = expression;
    }

    /**
     * Returns the mulitplicity of this.
     *
     * @return this.multiplicity
     */
    public Multiplicity multiplicity() {
        return multiplicity;
    }

    /**
     * Returns the expression of this.
     *
     * @return this.expression
     */
    public Expression expression() {
        return expression;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Formula#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> F accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    @Override
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#toString()
     */
    @Override
    public String toString() {
        return multiplicity + " " + expression;
    }
}
