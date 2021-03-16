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

import java.util.Arrays;
import java.util.Iterator;

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;

/**
 * A general projection expression. For example, let [[e]] = {&lt;a, b, c&gt;,
 * &lt;d, e, f&gt;, &lt;d, g, f&gt;}. Then, project(e, 1, 3) = {&lt;a, c&gt;,
 * &lt;d, f&gt;} and project(e, 1, 1, 2) = {&lt;a, a, b&gt;, &lt;d, d, e&gt;,
 * &lt;d, d, g&gt;}.
 *
 * @specfield expression: Expression
 * @specfield columns: [0..arity) -> one IntExpression
 * @invariant children = 0->expression + { i: int, e: IntExpression |
 *            columns[i-1] = e }
 * @author Emina Torlak
 */
public final class ProjectExpression extends Expression {

    private final Expression      expr;
    private final IntExpression[] columns;

    /**
     * Constructs a new projection expression using the given expr and columns.
     *
     * @ensures this.expression' = expr && this.indices' = columns
     */
    ProjectExpression(Expression expr, IntExpression... columns) {
        if (columns.length == 0)
            throw new IllegalArgumentException("No columns specified for projection.");
        this.expr = expr;
        this.columns = new IntExpression[columns.length];
        System.arraycopy(columns, 0, this.columns, 0, columns.length);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Expression#arity()
     */
    @Override
    public int arity() {
        return columns.length;
    }

    /**
     * Returns this.expression.
     *
     * @return this.expression
     */
    public Expression expression() {
        return expr;
    }

    /**
     * Returns an iterator over this.columns, in proper sequence.
     *
     * @return an iterator over this.columns, in proper sequence
     */
    public Iterator<IntExpression> columns() {
        return Containers.iterate(columns);
    }

    /**
     * Returns the ith column.
     *
     * @requires 0 <= i < this.arity
     * @return this.columns[i]
     */
    public IntExpression column(int i) {
        return columns[i];
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
        return expr.toString() + Arrays.toString(columns);
    }

}
