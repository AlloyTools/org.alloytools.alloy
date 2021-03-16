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

import kodkod.ast.operator.IntCastOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * Represents the conversion from an {@link kodkod.ast.IntExpression int
 * expression } to an {@link kodkod.ast.Expression expression}. The meaning of
 * the resulting expression is a singleton set containing the atom that
 * represents the integer given by the wrapped int expression, if the conversion
 * operator is INTCAST. Otherwise, the meaning is the set of powers of 2 that
 * make up the given integer expression.
 *
 * @specfield intExpr: IntExpression
 * @specfield op: IntCastOperator
 * @invariant children = 0->intExpr
 * @invariant arity = 1
 * @author Emina Torlak
 */
public final class IntToExprCast extends Expression {

    private final IntExpression   intExpr;
    private final IntCastOperator op;

    /**
     * Constructs a new IntToExprCast.
     *
     * @requires intExpr != null && op != null
     * @ensures this.intexpr' = intExpr
     */
    IntToExprCast(IntExpression intExpr, IntCastOperator op) {
        this.intExpr = intExpr;
        this.op = op;
    }

    /**
     * Returns 1.
     *
     * @return 1
     */
    @Override
    public int arity() {
        return 1;
    }

    /**
     * Returns this.intExpr.
     *
     * @return this.intExpr
     */
    public IntExpression intExpr() {
        return intExpr;
    }

    /**
     * Returns this.op
     *
     * @return this.op
     */
    public final IntCastOperator op() {
        return op;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Expression#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> E accept(ReturnVisitor<E,F,D,I> visitor) {
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
        return op + "[" + intExpr + "]";
    }

}
