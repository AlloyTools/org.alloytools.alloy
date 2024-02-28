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
package kodkod.util.ints;

import java.util.NoSuchElementException;

/**
 * A skeletal implementation of the IntSet interface.  
 * @author Emina Torlak
 */
public abstract class AbstractIntSet extends AbstractIntCollection implements IntSet {
	
	/**
	 * Constructs an empty int set.
	 * @ensures no this.ints'
	 */
	protected AbstractIntSet() {}
	
	/**
	 * Throws a NoSuchElementException if this is an empty set.
	 * @throws NoSuchElementException  this.isEmpty()
	 */
	final void checkNonEmpty() {
		if  (isEmpty()) throw new NoSuchElementException("no this.ints");
	}
	
	/**
	 * Returns an ascending iterator over all elements in this set.
	 * This method calls this.iterator(Integer.MIN_VALUE, Integer.MAX_VALUE).
	 * @return an ascending iterator over all elements in this set.
	 */
	public IntIterator iterator() {
		return iterator(Integer.MIN_VALUE, Integer.MAX_VALUE);
	}
		
	/**
	 * Returns the first element returned by this.iterator().
	 * If this set is empty, throws a NoSuchElementException().
	 * @return min(this.ints)
	 * @throws NoSuchElementException  no this.ints
	 */
	public int min() {
		return iterator().next();
	}
	
	/**
	 * Returns the first element returned by this.iterator(Integer.MAX_VALUE, Integer.MIN_VALUE).
	 * If this set is empty, throws a NoSuchElementException().
	 * @return max(this.ints)
	 * @throws NoSuchElementException  no this.ints
	 */
	public int max() {
		return iterator(Integer.MAX_VALUE, Integer.MIN_VALUE).next();
	}
		
	/**
	 * Returns the result of calling super.clone().
	 * @return the result of calling super.clone()
	 * @see java.lang.Object#clone()
	 */
	public IntSet clone() throws CloneNotSupportedException {
		return (IntSet) super.clone();
	}
	
	/**
     * Compares the specified object with this set for equality. 
     * Returns true if the specified object is also an IntSet, 
     * the two sets have the same size, and every member of the 
     * specified set is contained in this set (or equivalently, 
     * every member of this set is contained in the specified set). 
     * This definition ensures that the equals method works properly 
     * across different implementations of the IntSet interface.
     * @return o instanceof IntSet and o.size() = this.size() and this.containsAll(o)
     */
	public boolean equals(Object o) {
		if (o==this) return true;
		else if (o instanceof IntSet) {
			final IntSet s = (IntSet) o;
			return size()==s.size() && containsAll(s);
		} else return false;
	}
	
	/**
     * Returns the hash code value for this set. The hash code of a set is 
     * defined to be the {@link Ints#superFastHash(int[])} of the elements in the set, 
     * taken in the ascending order of values.  
     * This ensures that s1.equals(s2) implies that s1.hashCode()==s2.hashCode() 
     * for any two IntSets s1 and s2, as required by the general contract of the Object.hashCode method.
     * @return Ints.superFastHash(this.toArray())
     */
	public int hashCode() { 
		int hash = size();
		for(IntIterator iter = iterator(); iter.hasNext();) {
			hash = Ints.superFastHashIncremental(iter.next(), hash);
		}
		return Ints.superFastHashAvalanche(hash);
	}
	
	/**
	 * Returns a string representation of this int set.
	 * @return a string representation of this int set.
	 */
	public String toString() {
		final StringBuilder buf = new StringBuilder("{");
		final IntIterator itr = iterator();
		if (itr.hasNext()) buf.append(itr.next());
		while(itr.hasNext()) {
			buf.append(", ");
			buf.append(itr.next());
		}
		buf.append("}");
		return buf.toString();
	}
}
