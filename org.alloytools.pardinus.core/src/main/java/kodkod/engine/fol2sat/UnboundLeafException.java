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
package kodkod.engine.fol2sat;

import kodkod.ast.LeafExpression;

/**
 * Thrown when a node contains an undeclared variable or a relation with no bounds.
 * @specfield leaf: LeafExpression // the unbound leaf that caused the exception to be thrown
 * @author Emina Torlak
 */
public final class UnboundLeafException extends RuntimeException {
	private final LeafExpression leaf;
	private static final long serialVersionUID = 2472395272061454465L;

	/**
	 * Constructs an UnboundLeafException for the given leaf.
	 * @ensures this.leaf' = leaf
	 */
	UnboundLeafException(String msg, LeafExpression leaf) {
		super(msg + ": " +leaf);
		this.leaf = leaf;
	}

	/**
	 * Returns this.leaf.
	 * @return this.leaf
	 */
	public LeafExpression leaf() { 
		return leaf;
	}

}
