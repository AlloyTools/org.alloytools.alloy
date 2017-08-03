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

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A skeletal implementation of the SparseSequence interface.
 * The class provides an implementation for the <code>isEmpty</code>, 
 * <code>putAll</code>, <code>contains</code>, <code>indices</code>, <code>equals</code>, <code>hashCode</code>,
 * and <code>toString</code> methods.  All other methods must be
 * implemented by the subclasses. 
 * 
 * @specfield entries: int -> lone V
 * 
 * @author Emina Torlak
 */
public abstract class AbstractSparseSequence<V> implements SparseSequence<V> {

	/**
	 * Constructs a sparse sequence
	 * @ensures no this.entries'
	 */
	protected AbstractSparseSequence() {}
	
	/**
	 * Returns true if the size of this sequence is 0.
	 * @return this.size()==0
	 */
	public boolean isEmpty() { 
		return size()==0; 
	}
	
	/**
	 * Returns an iterator over the entries in this sequence
	 * in the ascending order of indeces, starting at this.first().
	 * This method calls this.iterator(Integer.MIN_VALUE, Integer.MAX_VALUE).
	 * @return an iterator over this.entries starting at the entry
	 * with the smallest index
	 */
	public Iterator<IndexedEntry<V>> iterator() {
		return iterator(Integer.MIN_VALUE, Integer.MAX_VALUE);
	}
	
	/**
	 * Returns the first element in this sequence, if any.  This
	 * method first checks that the sequence is not empty, and 
	 * if not, returns this.iterator().next();
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#first()
	 */
	public IndexedEntry<V> first() {
		return isEmpty() ? null : iterator().next();
	}

	/**
	 * Returns the last element in this sequence, if any.  This
	 * method first checks that the sequence is not empty, and 
	 * if not, returns this.iterator(Integer.MAX_VALUE, Integer.MIN_VALUE).next();
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#last()
	 */
	public IndexedEntry<V> last() {
		return isEmpty() ? null : iterator(Integer.MAX_VALUE, Integer.MIN_VALUE).next();
	}
	
	/**
	 * Returns the entry whose index is the ceiling of the given index in this sequence.
	 * This method calls this.iterator(index, Integer.MAX_VALUE), and if the resulting iterator has 
	 * a next element returns it. 
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#ceil(int)
	 */
	public IndexedEntry<V> ceil(int index) {
		final Iterator<IndexedEntry<V>> itr = iterator(index, Integer.MAX_VALUE);
		return itr.hasNext() ? itr.next() : null;
	}
	
	/**
	 * Returns the entry whose index is the floor of the given index in this sequence.
	 * This method calls this.iterator(index, Integer.MIN_VALUE), and if the resulting iterator has 
	 * a next element returns it. 
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#floor(int)
	 */
	public IndexedEntry<V> floor(int index) {
		final Iterator<IndexedEntry<V>> itr = iterator(index, Integer.MIN_VALUE);
		return itr.hasNext() ? itr.next() : null;
	}
	
	/**
	 * Returns the set of all indices mapped by this sparse sequence.
	 * The returned set supports removal iff this is not an unmodifiable
	 * sparse sequence.  
	 * @return {s: IntSet | s.ints = this.entries.V}
	 */
	public IntSet indices() {
		return new AbstractIntSet() {
			public IntIterator iterator(final int from, final int to) {
				return new IntIterator() {
					Iterator<IndexedEntry<V>> iter = AbstractSparseSequence.this.iterator(from, to);
					public boolean hasNext() {
						return iter.hasNext();
					}
					public int next() {
						return iter.next().index();
					}
					public void remove() {
						iter.remove();
					}
				};
			}
			public int size() {
				return AbstractSparseSequence.this.size();
			}
			public boolean contains(int i) {
				return containsIndex(i);
			}
			public int min() {
				final IndexedEntry<V> first = AbstractSparseSequence.this.first();
				if (first==null) 
					throw new NoSuchElementException();
				return first.index();
			}
			public int max() {
				final IndexedEntry<V> last = AbstractSparseSequence.this.last();
				if (last==null) 
					throw new NoSuchElementException();
				return last.index();
			}
			public boolean remove(int i) {
				final boolean isMapped = containsIndex(i);
				AbstractSparseSequence.this.remove(i);
				return isMapped;
			}
			public int floor(int i) {
				final IndexedEntry<V> floor = AbstractSparseSequence.this.floor(i);
				if (floor==null)
					throw new NoSuchElementException();
				return floor.index();
			}
			public int ceil(int i) {
				final IndexedEntry<V> ceil = AbstractSparseSequence.this.ceil(i);
				if (ceil==null)
					throw new NoSuchElementException();
				return ceil.index();
			}
			public void clear() {
				AbstractSparseSequence.this.clear();
			}
			public IntSet clone() throws CloneNotSupportedException { 
				final IntSet s;
				if (size()==0)
					s = Ints.bestSet(Integer.MIN_VALUE, Integer.MAX_VALUE);
				else 
					s = Ints.bestSet(min(), max());
				s.addAll(this);
				return s;
			}
		};
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#values()
	 */
	public Collection<V> values() {
		return new AbstractCollection<V>() {

			public int size() {
				return AbstractSparseSequence.this.size();
			}

			public boolean isEmpty() {
				return AbstractSparseSequence.this.isEmpty();
			}

			public boolean contains(Object arg0) {
				return AbstractSparseSequence.this.contains(arg0);
			}

			public Iterator<V> iterator() {
				return new Iterator<V>() {
					Iterator<IndexedEntry<V>> iter = AbstractSparseSequence.this.iterator();
					public boolean hasNext() {
						return iter.hasNext();
					}
					public V next() {
						return iter.next().value();
					}
					public void remove() {
						iter.remove();
					}
				};
			}
			
			public void clear() {
				AbstractSparseSequence.this.clear();
			}
		};
	}
	
	/**
	 * Returns true if this sparse sequence has an entry for the
	 * given index; otherwise returns false.  This method returns
	 * the value of this.iterator(index,index).hasNext();
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#containsIndex(int)
	 */
	public boolean containsIndex(int index) {
		return iterator(index,index).hasNext();
	}
	
	/**
	 * Iterates through all the entries in this sequence and returns 
	 * true if one of the encountered entries has the given object as
	 * its value.
	 * @return {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#contains(java.lang.Object)
	 */
	public boolean contains(Object value) {
		for(IndexedEntry<?> v: this) {
			if (equal(value, v.value()))
				return true;
		}
		return false;
	}
	
	/**
	 * Returns the result of calling super.clone().
	 * @see java.lang.Object#clone()
	 */
	@SuppressWarnings("unchecked")
	public SparseSequence<V> clone() throws CloneNotSupportedException {
		return (SparseSequence<V>) super.clone();
	}
	
	/*---------- adapted from java.util.AbstractMap -----------*/
		
	/**
	 * Removes the entry with the given index, if it exists, and
	 * returns the value previously stored at the index.  If the
	 * sequence had no previous mapping for the index, null is returned.
	 * This method obtains an iterator from index to index and removes
	 * its sole element, if any.
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#remove(int)
	 */
	public V remove(int index) {
		final Iterator<IndexedEntry<V>> itr = iterator(index,index);
		if (itr.hasNext()) {
			final V ret = itr.next().value();
			itr.remove();
			return ret;
		}
		return null;
	}
	
	/**
	 * Removes all entries from this sequences.  This method
	 * obtains an iterator over the sequences and calls remove()
	 * after each call to next().
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#clear()
	 */
	public void clear() {
		final Iterator<IndexedEntry<V>> itr = iterator();
		while(itr.hasNext()) {
			itr.next();
			itr.remove();
		}
	}
	
	
	/**
	 * Throws an UnsupportedOperationException.
	 * @throws UnsupportedOperationException
	 */
	public V put(int index, V value) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Copies all of the entries from the specified sparse sequence to 
	 * this sequence. This implementation calls put(e.index, e.value) on 
	 * this sequence once for each entry e in the specified sequence. 
     * @ensures this.entries' = this.entries ++ s.entries
	 */
	public void putAll(SparseSequence<? extends V> s) {
		Iterator<? extends IndexedEntry<? extends V>> i = s.iterator();
		while (i.hasNext()) {
			IndexedEntry<? extends V> e = i.next();
			put(e.index(), e.value());
		}
	}
	
	/**
	 * Returns true if both o1 and o2 are null, or 
	 * o1.equals(o2)
	 * @return o1 and o2 are equal
	 */
	static boolean equal(Object o1, Object o2) {
		return o1==null ? o2==null : o1.equals(o2);
	}
	
	/**
	 * Returns true if the indexed entries e0 and e1 are equal to each other.
	 * @requires e0 != null && e1 != null
	 * @return e0.index = e1.index && e0.value = e1.value
	 */
	static boolean equal(IndexedEntry<?> e0, IndexedEntry<?> e1) {
		return e0.index()==e1.index() && equal(e0.value(), e1.value());
	}
	
	/**
	 * Compares the specified object with this sequence for equality.  Returns
	 * <tt>true</tt> if the given object is also a sequence and the two sequences
	 * represent the same function from integers to E.<p>
	 *
	 * This implementation first checks if the specified object is this sequence;
	 * if so it returns <tt>true</tt>.  Then, it checks if the specified
	 * object is a sequence whose size is identical to the size of this set; if
	 * not, it returns <tt>false</tt>.  If so, it iterates over this sequences's
	 * entries, and checks that the specified sequence
	 * contains each entry that this sequence contains.  If the specified sequence
	 * fails to contain such an entry, <tt>false</tt> is returned.  If the
	 * iteration completes, <tt>true</tt> is returned.
	 * @return  o in SparseSequence && o.entries = this.entries
	 */
	@SuppressWarnings("unchecked")
	public boolean equals(Object o) {
		if (o == this) return true;
		
		if (!(o instanceof SparseSequence)) return false;
		
		SparseSequence<V> s = (SparseSequence<V>) o;
		if (s.size() != size()) return false;
		
		try {
			final Iterator<IndexedEntry<V>> i1 = iterator(), i2 = s.iterator();
			while (i1.hasNext()) {
				if (!equal(i1.next(), i2.next())) 
					return false;
			}
		} catch(ClassCastException unused) {
			return false;
		} catch(NullPointerException unused) {
			return false;
		}
		
		return true;
	}
	
	/**
	 * Returns the hashcode for an indexed entry.
	 * @requires e !=  null
	 * @return e.index ^ e.value.hashCode()
	 */
	static int hashCode(IndexedEntry<?> e) {
		return e.index() ^ (e.value()==null ? 0 : e.value().hashCode());
	}
	
	/**
	 * Returns the hash code value for this sparse sequence. 
	 * The hash code of a sparse sequence is defined to be the sum of the 
	 * hashCodes of each entry of its entries. This ensures that t1.equals(t2) 
	 * implies that t1.hashCode()==t2.hashCode() for any two sequences t1 and t2, 
	 * as required by the general contract of Object.hashCode.
	 * This implementation iterates over this.entries, calling
	 * <tt>hashCode</tt> on each IndexedEntry in the sequence, and adding
	 * up the results.
	 * @return sum(this.entries.hashCode())
	 */
	public int hashCode() {
		int h = 0;
		for (IndexedEntry<V> e : this)
			h += hashCode(e);
		return h;
	}
	
	/**
	 * Returns a string representation of this sequence.  The string representation
	 * consists of a list of index-value mappings in the order returned by the
	 * sequences <tt>iterator</tt>, enclosed in brackets
	 * (<tt>"[]"</tt>).  Adjacent entries are separated by the characters
	 * <tt>", "</tt> (comma and space).  Each index-value mapping is rendered as
	 * the index followed by an equals sign (<tt>"="</tt>) followed by the
	 * associated value.  Elements are converted to strings as by
	 * <tt>String.valueOf(Object)</tt>.<p>
	 *
	 * This implementation creates an empty string buffer, appends a left
	 * bracket, and iterates over the map's entries, appending
	 * the string representation of each <tt>IndexedEntry</tt> in turn.  After
	 * appending each entry except the last, the string <tt>", "</tt> is
	 * appended.  Finally a right bracket is appended.  A string is obtained
	 * from the stringbuffer, and returned.
	 *
	 * @return a String representation of this map.
	 */
	public String toString() {
		final StringBuilder buf = new StringBuilder();
		buf.append("[");
		
		final Iterator<IndexedEntry<V>> i = iterator();
		boolean hasNext = i.hasNext();
		while (hasNext) {
			IndexedEntry<V> e = i.next();
			buf.append(e.index());
			buf.append("=");
			if (e.value() == this)
				buf.append("(this sequence)");
			else
				buf.append(e.value());
			hasNext = i.hasNext();
			if (hasNext) buf.append(", ");
		}
		
		buf.append("]");
		return buf.toString();
	}

	
}
