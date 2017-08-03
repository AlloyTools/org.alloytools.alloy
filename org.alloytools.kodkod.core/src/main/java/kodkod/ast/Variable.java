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
 * Represents a variable in a {@link QuantifiedFormula quantified formula}, 
 * a {@link Comprehension comprehension expression}, or a {@link SumExpression sum expression}.  
 * Two variables are the same if and only if they
 * refer to the same object.  That is, v1.eauls(v2) <=> v1 == v2.  Each
 * variable has a name, which is basically a comment for the purpose of 
 * printing, viewing, etc.  The name has no meaning otherwise.  The arity of
 * a variable specifies the arity of expressions over which the variable can
 * range.
 * 
 * @specfield name: String
 * @specfield arity: int
 * @invariant no children
 * @author Emina Torlak 
 */
public final class Variable extends LeafExpression {

	/**
	 * Constructs a variable with the specified name and arity 1.
	 * @ensures this.name' = name && this.arity' = 1
	 */
	private Variable(String name) {
		super(name, 1);
	}

	/**
	 * Constructs a variable with the specified name and arity.
	 * @ensures this.name' = name && this.arity' = arity
	 */
	private Variable(String name, int arity) {
		super(name, arity);
	}

	/**
	 * Returns a new variable with the specified name and arity 1.
	 * @ensures this.name' = name && this.arity' = 1
	 */
	public static Variable unary(String name) {
		return new Variable(name);
	}

	/**
	 * Returns a new variable with the specified name and arity.
	 * @ensures this.name' = name && this.arity' = arity
	 * @throws IllegalArgumentException  arity < 1
	 */
	public static Variable nary(String name, int arity) {
		return new Variable(name, arity);
	}

	/**
	 * Returns the declaration that constrains this variable to 
	 * be bound to at most one element of the given expression:  'this: lone expr'.
	 * @return {d: Decl | d.variable = this && d.multiplicity = LONE && d.expression = expr }
	 * @throws NullPointerException  expr = null
	 * @throws IllegalArgumentException  this.arity != expr.arity || expr.arity != 1
	 */
	public Decl loneOf(Expression expr) {
		return new Decl(this, Multiplicity.LONE, expr);
	}

	/**
	 * Returns the declaration that constrains this variable to 
	 * be bound to exactly one element of the given expression:  'this: one expr'.
	 * @return {d: Decl | d.variable = this && d.multiplicity = ONE && d.expression = expr }
	 * @throws NullPointerException  expr = null
	 * @throws IllegalArgumentException  this.arity != expr.arity || expr.arity != 1
	 */
	public Decl oneOf(Expression expr) {
		return new Decl(this, Multiplicity.ONE, expr);
	}

	/**
	 * Returns the declaration that constrains this variable to 
	 * be bound to at least one element of the given expression:  'this: some expr'.
	 * @return {d: Decl | d.variable = this && d.multiplicity = SOME && d.expression = expr }
	 * @throws NullPointerException  expr = null
	 * @throws IllegalArgumentException  this.arity != expr.arity || expr.arity != 1
	 */
	public Decl someOf(Expression expr) {
		return new Decl(this, Multiplicity.SOME, expr);
	}

	/**
	 * Returns the declaration that constrains this variable to 
	 * be bound to a subset of the elements in the given expression:  'this: set expr'.
	 * @return {d: Decl | d.variable = this && d.multiplicity = SET && d.expression = expr }
	 * @throws NullPointerException  expr = null
	 * @throws IllegalArgumentException  this.arity != expr.arity 
	 */
	public Decl setOf(Expression expr) {
		return new Decl(this, Multiplicity.SET, expr);
	}

	/**
	 * Returns the declaration that constrains this variable to 
	 * be bound to the specified number of the elements in the given expression:  'this: mult expr'.
	 * @return {d: Decl | d.variable = this && d.multiplicity = mult && d.expression = expr }
	 * @throws NullPointerException  expression = null || mult = null
	 * @throws IllegalArgumentException  mult = NO
	 * @throws IllegalArgumentException  mult in ONE + LONE + SOME && expr.arity != 1
	 * @throws IllegalArgumentException  this.arity != expr.arity
	 */
	public Decl declare(Multiplicity mult, Expression expr) {
		return new Decl(this, mult, expr);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Expression#accept(kodkod.ast.visitor.ReturnVisitor)
	 */
	public <E, F, D, I> E accept(ReturnVisitor<E, F, D, I> visitor) {
		return visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
	 */
	public void accept(VoidVisitor visitor) {
		visitor.visit(this);
	}

}
