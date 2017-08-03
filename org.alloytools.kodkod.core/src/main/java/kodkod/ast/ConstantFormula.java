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
 * A constant {@link kodkod.ast.Formula formula}, true or false.
 *
 * @invariant no children
 * @author Emina Torlak 
 */
public abstract class ConstantFormula extends Formula {
	private final boolean value;
	/**
	 * Constructs a constant formula with the given value.
	 */
	ConstantFormula(boolean value) {
		this.value = value;
	}
    
	/**
	 * Returns the boolean value that corresponds to this 
	 * constant formula.
	 * @return this=TRUE => true, false
	 */
	public final boolean booleanValue() { return value; }
	
	 /**
	    * {@inheritDoc}
	    * @see kodkod.ast.Formula#accept(kodkod.ast.visitor.ReturnVisitor)
	    */
	    public <E, F, D, I> F accept(ReturnVisitor<E, F, D, I> visitor) {
	        return visitor.visit(this);
	    }
	    
	    /**
	     * {@inheritDoc}
	     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
	     */
	    public void accept(VoidVisitor visitor) {
	        visitor.visit(this);
	    }
	    
	    /**
	     * {@inheritDoc}
	     * @see kodkod.ast.Node#toString()
	     */
	public String toString() {
		return String.valueOf(booleanValue());
	}
}

