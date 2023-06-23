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

import java.util.Iterator;

import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;

/** 
 * A relational {@linkplain kodkod.ast.Expression expression} with more than two children,
 * composed with an nary {@linkplain ExprOperator  operator}.
 * 
 * @specfield op: ExprOperator
 * @invariant op.nary()
 * @invariant #children > 2
 * @author Emina Torlak 
 */
public final class NaryExpression extends Expression implements Iterable<Expression>{
	private final ExprOperator op;
	private final int arity;
	private final Expression[] children;
	
	/**  
	 * Constructs a new associative expression: op(children)
	 * @requires children array is not modified while in use by this associative expression
	 * @requires some op.op[children]
	 * @ensures this.children' = children && this.op' = op
	 */
	NaryExpression(ExprOperator op, Expression[] children) {
		assert children.length>2;
		if (!op.nary()) 
			throw new IllegalArgumentException("Cannot construct an nary expression using the non-nary operator " + op);
		
		this.op = op;
		this.children = children;
		
		switch(op) { 
		case UNION : case INTERSECTION : case OVERRIDE :		
			this.arity = children[0].arity();
			for(int i = 1; i < children.length; i++) { 
				if (children[i].arity()!=arity)
					throw new IllegalArgumentException("Incompatible arities: " + children[0] + " and " + children[i]);
			}
			break;
		case PRODUCT : 		
			int sum = 0; 
			for(Expression child : children) { sum += child.arity(); }
			this.arity = sum; 
			break;
		default :  			
			throw new IllegalArgumentException("Unknown associative operator: " + op);
		}
	}
	
	/**
	 * Returns the arity of this associative expression.
	 * @return this.arity
	 * @see kodkod.ast.Expression#arity()
	 */
	public final int arity() { return arity; }

	/**
	 * Returns this.op.
	 * @return this.op
	 */
	public ExprOperator op() { return op ; }
	
	
	/**
	 * Returns the number of children of this expression.
	 * @return #this.children
	 */
	public int size() { return children.length; }
	
	/**
	 * Returns the ith child of this associative expression.
	 * @requires 0 <= i < #this.children
	 * @return this.children[i]
	 */
	public Expression child(int i) { return children[i]; }
	
	/**
	 * Returns an iterator over this expression's children,
	 * in the increasing order of indices.
	 * @return an iterator over this expression's children,
	 * in the increasing order of indices.
	 */
	public Iterator<Expression> iterator() { return Containers.iterate(children); }
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Expression#accept(kodkod.ast.visitor.ReturnVisitor)
	 */
	@Override
	public <E, F, D, I> E accept(ReturnVisitor<E, F, D, I> visitor) {
		return visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
	 */
	@Override
	public void accept(VoidVisitor visitor) {
		visitor.visit(this);	
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder s = new StringBuilder("(");
		s.append(child(0));
		for(int i = 1, size = size(); i < size; i++) { 
			s.append(" ");
			s.append(op);
			s.append(" ");
			s.append(child(i));
		}
		s.append(")");
		return s.toString();
	}


}
