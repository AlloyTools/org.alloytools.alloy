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


import kodkod.ast.operator.ExprCastOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * An {@link kodkod.ast.IntExpression } representing the 
 * cardinality of an {@link kodkod.ast.Expression} or the 
 * sum of all the integer atoms contained in the expression.
 * @specfield expression: Expression
 * @specfield op: ExprCastOperator
 * @invariant children = 0->expression
 * @author Emina Torlak
 */
public final class ExprToIntCast extends IntExpression {
	private final Expression expression;
	private final ExprCastOperator op; 
	/**  
	 * Constructs a new cardinality expression.
	 * 
	 * @ensures this.expression' = expression && this.op' = op
	 * @throws NullPointerException  expression = null || op = null
	 * @throws IllegalArgumentException  op = SUM && child.arity != 1
	 */
	ExprToIntCast(Expression child, ExprCastOperator op) {
		if (child.arity()>1 && op==ExprCastOperator.SUM) 
			throw new IllegalArgumentException("cannot apply " + op + " to " + child);
		this.expression = child;
		this.op = op;
	}
	
	/**
	 * Returns this.expression.
	 * @return this.expression
	 */
	public Expression expression() {return expression;}

	/**
	 * Returns this.op.
	 * @return this.op
	 */
	public ExprCastOperator op() { return op; } 
	
		
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
		return op + "("+expression.toString()+")";
	}
	
}
