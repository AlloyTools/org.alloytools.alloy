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
 * Denotes the integer obtained by summing the values of an iteger expression
 * <i>ie</i> for all values of a scalar <i>x</i> drawn from a set <i>e</i>.
 *
 * @specfield intExpr: IntExpression
 * @specfield decls: Decls
 * @specfield children = 0->decls + 1->intExpr
 * @invariant all d: decls.children[int] | d.multiplicity = 1
 * @author Emina Torlak
 */
public final class SumExpression extends IntExpression {

    private final Decls         decls;
    private final IntExpression intExpr;

    /**
     * Constructs a sum expression
     *
     * @ensures this.decls' = decls && this.intExpr' = intExpr
     * @throws IllegalArgumentException some d: decls.children | d.multiplicty !=
     *             ONE
     */
    SumExpression(Decls decls, IntExpression intExpr) {
        for (Decl d : decls) {
            if (d.multiplicity() != Multiplicity.ONE)
                throw new IllegalArgumentException(d + " is not a scalar declaration.");
        }
        this.decls = decls;
        this.intExpr = intExpr;
    }

    /**
     * Returns this.decls.
     *
     * @return this.decls
     */
    public final Decls decls() {
        return decls;
    }

    /**
     * Returns this.intExpr.
     *
     * @return this.intExpr
     */
    public final IntExpression intExpr() {
        return intExpr;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> I accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.VoidVisitor)
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
        return "(sum " + decls + " | " + intExpr + ")";
    }

}
