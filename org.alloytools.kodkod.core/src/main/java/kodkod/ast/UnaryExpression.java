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

import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * An {@link kodkod.ast.Expression expression} with one child.
 *
 * @specfield expression: Expression
 * @specfield op: ExprOperator
 * @invariant op.unary()
 * @invariant children = 0->Expression
 * @author Emina Torlak
 */
public final class UnaryExpression extends Expression {

    private final Expression   expression;
    private final ExprOperator op;
    private final int          arity;

    /**
     * Constructs a new unary expression: op expression
     *
     * @ensures this.expression' = expression && this.op' = op
     * @throws NullPointerException expression = null || op = null
     * @throws IllegalArgumentException op in {TRANSPOSE, CLOSURE,
     *             REFLEXIVE_CLOSURE} && child.arity != 2
     */
    UnaryExpression(ExprOperator op, Expression child) {
        if (!op.unary()) {
            throw new IllegalArgumentException("Not a unary operator: " + op);
        }
        if (child.arity() != 2 && op != ExprOperator.PRE) {
            throw new IllegalArgumentException("Invalid arity: " + child + "::" + child.arity());
        }
        this.expression = child;
        this.op = op;
        this.arity = child.arity();
    }

    /**
     * Returns the arity of this expression.
     *
     * @return this.arity
     * @see kodkod.ast.Expression#arity()
     */
    @Override
    public int arity() {
        return arity;
    }

    /**
     * Returns this.expression.
     *
     * @return this.expression
     */
    public Expression expression() {
        return expression;
    }

    /**
     * Returns this.op.
     *
     * @return this.op
     */
    public ExprOperator op() {
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
        return op.toString() + expression.toString();
    }

}
