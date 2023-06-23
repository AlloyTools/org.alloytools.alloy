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

import kodkod.ast.operator.IntOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * A unary integer intExpr, e.g. -x.
 * @specfield intExpr: IntExpression
 * @specfield op: IntOperator
 * @invariant op.unary()
 * @invariant children = 0->intExpr
 * @author Emina Torlak
 */
public final class UnaryIntExpression extends IntExpression {
	private final IntOperator op;
	private final IntExpression intExpr;
	
	/**
	 * Constructs a new unary int formula: op intExpr
	 * @ensures this.op' = op && this.intExpr' = intExpr
	 */
	UnaryIntExpression(IntOperator op, IntExpression intExpr) {
		if (!op.unary()) throw new IllegalArgumentException("Not a unary operator: " + op);
		this.op = op;
		this.intExpr = intExpr;
	}

	/**
	 * Returns the operator of this.
	 * @return this.op
	 */
	public IntOperator op() {return op;}
	
	/**
	 * Returns this.intExpr.
	 * @return this.intExpr
	 */
	public IntExpression intExpr() {return intExpr;}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.ReturnVisitor)
	 */
	@Override
	public <E, F, D, I> I accept(ReturnVisitor<E, F, D, I> visitor) {
		return visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.VoidVisitor)
	 */
	@Override
	public void accept(VoidVisitor visitor) {
		visitor.visit(this);
	}

	/**
     * {@inheritDoc}
     * @see kodkod.ast.Node#toString()
     */
	public String toString() {
		return (op==IntOperator.NEG||op==IntOperator.NOT) ? "(" + op + intExpr + ")" : op + "(" + intExpr + ")" ;
	}
}
