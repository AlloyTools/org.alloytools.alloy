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

import java.util.Iterator;
import java.util.Set;



/**
 * A non-constant boolean value with zero or more inputs. 
 * @specfield op: Operator
 * @specfield size: int
 * @specfield inputs: [0..size) -> one BooleanFormula
 * @invariant size >= 0
 * @author Emina Torlak
 */
public abstract class BooleanFormula extends BooleanValue implements Iterable<BooleanFormula> {
	private BooleanFormula negation;
	
	/**
	 * Constructs a boolean formula with the given negation.
	 */
	BooleanFormula(BooleanFormula negation) { 
		this.negation = negation;
	}
	/**
	 * Returns an integer hash of this formula, used
	 * to compute the hash of the composition of this and
	 * some other formula with the given operator.    
	 * @return an integer hash of this formula when acting
	 * as an input to a multigate with the given operator.
	 */
	abstract int hash(Operator op); 
	
	/**
	 * Returns an integer k' such that 0 < |k'| < k and |k'| is the number of flattening
	 * steps that need to be taken to determine that this circuit has (or does not have)
	 * an input with the given label.
	 * A positive k' indicates that f is found to be an input to this circuit in k' steps.
	 * A negative k' indicates that f is not an input to this circuit, when it is flattened
	 * using at most k steps.  
	 * @requires k > 0
	 * @return the number of flattening
	 * steps that need to be taken to determine that f is (not) an input to this circuit
	 */
	int contains(Operator op, int f, int k) {
		return f==label() ? 1 : -1;
	}
	
	/**
	 * Flattens this circuit with respect to the given operator into 
	 * the provided set.  
	 * Specifically, the method modifies the set so that it contains
	 * the elements f_0, ..., f_k' where k' <= k elements and 
	 * [[this]] = op(f_0, ..., f_k').
	 * The default implementation simply adds this to the set.
	 * @requires k > 0
	 * @ensures 1 <= k' <= k && some f_0,..., f_k' : flat.elts' | 
	 * [[this]] = op([[f_0]], ..., [[f_k']])
	 */
	void flatten(Operator op, Set<BooleanFormula> flat, int k) {
		assert k > 0;
		flat.add(this);
	}
	
	
	
	/**
	 * Returns the negation of this formula if it has already been computed.
	 * Otherwise, computes, caches and returns the negation of this formula.
	 * @return !this
	 * @see kodkod.engine.bool.BooleanValue#negation()
	 */
	final BooleanFormula negation() {
		if (negation==null) {
			negation = new NotGate(this);
		}
		return negation;
	}
	
	/**
	 * Returns true if the negation of this formula 
	 * has already been computed.
	 * @return true if the negation of this formula has already been computed.
	 */
	final boolean hasNegation()  { return negation != null; }

	/**
	 * Passes this value and the given
	 * argument value to the visitor, and returns the resulting value.
	 * @return the value produced by the visitor when visiting this node
	 * with the given argument.
	 */
	public abstract <T, A> T accept(BooleanVisitor<T, A> visitor, A arg);
	
	
	
	/**
	 * Returns an iterator over the inputs to this gate.
	 * @return an iterator over this.inputs.
	 */
	public abstract Iterator<BooleanFormula> iterator();
	
	
	/**
	 * Returns the number of inputs to this gate.
	 * @return #this.inputs
	 */
	public abstract int size();
	
	/**
	 * Returns the ith input to this gate.
	 * @return this.inputs[i]
	 * @requires 0 <= i < size
	 * @throws IndexOutOfBoundsException  i < 0 || i >= #this.inputs
	 */
	public abstract BooleanFormula input(int i);
	
}
