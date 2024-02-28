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
package kodkod.engine.bool;

/**
 * A boolean constant, true or false.  The integer
 * label of the true and false constants are Integer.MAX_VALUE and -Integer.MAX_VALUE, respectively. 
 * The two boolean constants, TRUE and FALSE, are shared among all factories.
 * 
 * @specfield value: boolean
 * @invariant this.op = Operator.CONST
 * @invariant value => Integer.MAX_VALUE, -Integer.MAX_VALUE
 * @author Emina Torlak
 */
public final class BooleanConstant extends BooleanValue {
	final int label;
	
	public static final BooleanConstant TRUE = new BooleanConstant(true);
	public static final BooleanConstant FALSE = new BooleanConstant(false);
	
	/**
	 * Constructs a BooleanConstant that represent the given boolean
	 * value.
	 * @ensures value => this.label' = Integer.MAX_VALUE, this.label' = -Integer.MAX_VALUE
	 */
	private BooleanConstant(boolean value) {
		this.label = (value ? Integer.MAX_VALUE : -Integer.MAX_VALUE);
	}
	
	/**
	 * Returns the negation of this value.
	 * @return c: BooleanConstant | [[c]] = ![[this]]
	 */
	@Override
	BooleanValue negation() {
		return this==TRUE ? FALSE : TRUE;
	}
	
	/**
	 * Returns the primitive boolean representation of this label.
	 * @return this.label == Integer.MAX_VALUE
	 */
	public boolean booleanValue() { return label > 0; } 
	
	/**
	 * Returns the BooleanConstant that represents the given boolean value.
	 * @return {c: BooleanConstant | value => c.label = Integer.MAX_VALUE, c.label = -Integer.MAX_VALUE }
	 */
	public static BooleanConstant constant(boolean value) {
		return value ? TRUE : FALSE;
	}
	
	/**
	 * Returns the label for this value. 
	 * @return this.label
	 */
	@Override
	public int label() {
		return label;
	}

	/**
	 * Returns a string representation of this boolean value.
	 * @return a string representation of this boolean value.
	 */
	public String toString() {
		return label>0 ? "T" : "F";
	}

	/**
	 * Returns Operator.CONST.
	 * @return Operator.CONST
	 */
	@Override
	public Operator op() {
		return Operator.CONST;
	}


}
