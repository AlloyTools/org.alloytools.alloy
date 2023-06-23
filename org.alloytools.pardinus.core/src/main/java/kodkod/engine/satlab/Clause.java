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
package kodkod.engine.satlab;

import java.util.Iterator;

import kodkod.util.ints.IntIterator;
import kodkod.util.ints.Ints;

/**
 * A propositional clause.
 * 
 * @specfield literals: set int
 * @specfield antecedents: Clause[]
 * @invariant 0 !in literals 
 * @invariant no lit: literals | -lit in literals
 * @invariant some antecedents => #antecedents > 1
 * @invariant some antecedents => 
 *  literals = { lit: antecedents[int].literals | 
 *   no i: [0..#antecedents-1) | lit in antecedents[i].literals && -lit in antecedents[i+1].literals }
 * @author Emina Torlak
 */
public abstract class Clause {
	/**
	 * Constructs a new clause.
	 */
	protected Clause() {}
		
	/**
	 * Returns the size of this clause, measured in the 
	 * number of literals.
	 * @return #this.literals 
	 */
	public abstract int size();

	/**
	 * Returns an iterator over the literals in this clause, 
	 * in the ascending order of absolute values.
	 * @return an iterator over this.literals
	 */
	public abstract IntIterator literals();
	
	/**
	 * Returns the largest variable identifier occurring in this.literals.
	 * @return max(abs(this.literals))
	 */ 
	public abstract int maxVariable();
	
	/**
     * Copies this.literals into the specified array, provided
     * that it is large enough, and returns it.  If the array is not large enough,
     * a new array is allocated, populated with this.literals, and returned.
     * @return the given array, filled with this.literals, if
     * the it is large enough; otherwise a new array containing this.literals
     * @throws NullPointerException  array = null
     */
	public abstract int[] toArray(int[] array);
	
	/**
	 * Returns a new array of length this.size(), initialized with this.literals.
	 * @return a new array of length this.size(), initialized with this.literals.
	 */
	public int[] toArray() {
		return toArray(new int[size()]);
	}
	
	/**
	 * Returns the number of antecedents of this clause.
	 * @return #this.antecedents
	 */
	public abstract int numberOfAntecedents();
	
	/**
	 * Returns an iterator that traverses this.antecedents in proper sequence.
	 * <p><b>Note:</b>The clause objects returned by the iterator are not 
	 * required to be immutable.  In particular, the state of a clause object 
	 * returned by <tt>next()</tt> (as well as the state of any  object obtained
	 * through that clause's {@linkplain Clause#antecedents()} methods) is guaranteed 
	 * to remain the same only until the subsequent call to <tt>next()</tt>.</p>
	 * @return an iterator that traverses this.antecedents in proper sequence.
	 */
	public abstract Iterator<Clause> antecedents();
	
	/**
//	 * Returns the antecedent at the given index.
//	 * @requires 0 <= index < this.numberOfAntecedents()
//	 * @return this.antecedents[index]
//	 * @throws IndexOutOfBoundsException  index < 0 || index >= this.numberOfAntecedents()
//	 */
//	public abstract Clause antecedent(int index);
	
	/**
	 * Returns true if o is a Clause whose literals and antecedents
	 * are <tt>equal</tt> to those of this clause.
	 * @return o in Clause && o.literals.equals(this.literals) && o.antecedents.equals(this.antecedents)
	 */
	public boolean equals(Object o) {
		if (o==this) return true;
		if (o instanceof Clause) {
			final Clause c = (Clause) o;
			if (size()==c.size()) {
				final IntIterator itr1 = literals(), itr2 = literals();
				while(itr1.hasNext()) {
					if (itr1.next()!=itr2.next()) return false;
				}
			}
			final int ante = numberOfAntecedents();
			if (ante > 0 && ante==c.numberOfAntecedents()) {
				final Iterator<Clause> itr1 = antecedents(), itr2 = c.antecedents();
				while(itr1.hasNext()) {
					if (!itr1.next().equals(itr2.next())) return false;
				}
			}
			return ante==0;
		}
		return false;
	}
	
	/**
	 * Returns the hashcode for this clause.  The hashcode for a clause is equivalent
	 * to Ints.superFastHash(x) where x is an array such that its first this.size() 
	 * elements are the literals of this clause (as returned by this.literals()) 
	 * and its remaining this.numberOfAntecedents() elements are the hashCodes of 
	 * this.antecedents (as returned by this.antecedents()).
	 * @return hashcode for this clause
	 */
	public int hashCode() {
		int hash = size() + numberOfAntecedents();
		for(IntIterator iter = literals(); iter.hasNext(); ) {
			hash = Ints.superFastHashIncremental(iter.next(), hash);
		}
		for(Iterator<Clause> iter = antecedents(); iter.hasNext(); ) {
			hash = Ints.superFastHashIncremental(iter.next().hashCode(), hash);
		}
		return Ints.superFastHashAvalanche(hash);
	}

	/**
	 * Returns a string representation of this clause.
	 * @return a string representation of this clause.
	 */
	public String toString() {
		final StringBuilder ret = new StringBuilder();
		if (numberOfAntecedents()==0) {
			ret.append("AXIOM");
		} else {
			ret.append("RESOLVENT");
		}
		ret.append(". Literals: {");
		for(IntIterator iter = literals(); iter.hasNext();) {
			ret.append(" ");
			ret.append(iter.next());
		}
		ret.append(" }");
		return ret.toString();
	}
}