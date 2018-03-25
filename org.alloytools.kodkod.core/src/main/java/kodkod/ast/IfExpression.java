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

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * An expression whose value depends on the truth of a given condition.
 *
 * @specfield condition: Formula
 * @specfield thenExpr: Expression
 * @specfield elseExpr: Expression
 * @invariant children = 0->condition + 1->thenExpr + 2->elseExpr
 * @author Greg Dennis (gdennis@mit.edu)
 * @author Emina Torlak
 */
public final class IfExpression extends Expression {

    private final Formula    condition;
    private final Expression thenExpr, elseExpr;
    private final int        arity;

    /**
     * @ensures this.condition' = condition && this.thenExpr' = thenExpr &&
     *          this.elseExpr' = elseExpr
     * @throws IllegalArgumentException thenExpr.arity != elseExpr.arity
     */
    IfExpression(Formula condition, Expression thenExpr, Expression elseExpr) {
        if (thenExpr.arity() != elseExpr.arity()) {
            throw new IllegalArgumentException("Arity mismatch: " + thenExpr + "::" + thenExpr.arity() + " and " + elseExpr + "::" + elseExpr.arity());
        }
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
        this.arity = thenExpr.arity();
    }

    /**
     * Returns the if-condition.
     *
     * @return this.condition
     */
    public Formula condition() {
        return condition;
    }

    /**
     * Returns the then-expression.
     *
     * @return this.thenExpr
     */
    public Expression thenExpr() {
        return thenExpr;
    }

    /**
     * Returns the else-expression.
     *
     * @return this.elseExpr
     */
    public Expression elseExpr() {
        return elseExpr;
    }

    /**
     * Returns the arity of this.
     *
     * @return this.arity
     */
    @Override
    public int arity() {
        return arity;
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
        return "(if " + condition + " then " + thenExpr + " else " + elseExpr + ")";
    }

}
