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
package kodkod.util.collections;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Implements the <tt>Set</tt> interface, backed by a hash table.  
 * It makes no guarantees as to the
 * iteration order of the set; in particular, it does not guarantee that the
 * order will remain constant over time.  This class does not permit the <tt>null</tt>
 * element.<p>
 *
 * This class offers constant time performance for the basic operations
 * (<tt>add</tt>, <tt>remove</tt>, <tt>contains</tt> and <tt>size</tt>),
 * assuming the hash function disperses the elements properly among the
 * buckets.  Iterating over this set requires time proportional to the sum of
 * the <tt>HashSet</tt> instance's size (the number of elements) plus the
 * "capacity" of the backing map (the number of
 * buckets).  Thus, it's very important not to set the initial capacity too
 * high (or the load factor too low) if iteration performance is important.<p>
 *
 * <p>This set differs from Java's HashSet in that it provides methods for 
 * retrieving elements with a particular <tt>hashcode</tt>.  This makes it 
 * easy to set as a cache in which cached objects' hashcodes are their keys.</p>
 * 
 * <p><b>Note that this implementation is not synchronized.</b> 
 * The iterators returned by this class's <tt>iterator</tt> method are
 * not <i>fail-fast</i></p>
 *
 * @specfield elts: set T
 * @author Emina Torlak
 */
public final class CacheSet<E> extends AbstractSet<E> {
	/* implementation adapted from java.util.HashMap and java.util.HashSet */
	/**
	 * The default initial capacity - MUST be a power of two.
	 */
	private static final int DEFAULT_INITIAL_CAPACITY = 16;
	
	/**
	 * The maximum capacity, used if a higher value is implicitly specified
	 * by either of the constructors with arguments.
	 * MUST be a power of two <= 1<<30.
	 */
	private static final int MAXIMUM_CAPACITY = 1 << 30;
	
	/**
	 * The load factor used when none specified in constructor.
	 **/
	private static final float DEFAULT_LOAD_FACTOR = 0.75f;
	
	/**
	 * The table, resized as necessary. Length MUST Always be a power of two.
	 */
	private Entry<E>[] table;
	
	/**
	 * The number of key-value mappings contained in this identity hash map.
	 */
	private int size;
	
	/**
	 * The next size value at which to resize (capacity * load factor).
	 */
	private int threshold;
	
	/**
	 * The load factor for the hash table.
	 */
	final float loadFactor;
	
	/**
	 * Constructs a new, empty set; the backing map has
	 * default initial capacity (16) and load factor (0.75).
	 * @ensures no this.elts'
	 */
	@SuppressWarnings("unchecked")
	public CacheSet() {
		loadFactor = DEFAULT_LOAD_FACTOR;
		threshold = (int)(DEFAULT_INITIAL_CAPACITY * DEFAULT_LOAD_FACTOR);
		table = new Entry[DEFAULT_INITIAL_CAPACITY];
	}
	
	/**
	 * Constructs a new, empty set; the backing map has
	 * the specified initial capacity and the specified load factor.
	 *
	 * @param      initialCapacity   the initial capacity of the hash map.
	 * @param      loadFactor        the load factor of the hash map.
	 * @throws     IllegalArgumentException if the initial capacity is less
	 *             than zero, or if the load factor is nonpositive.
	 * @ensures no this.elts'
	 */
	@SuppressWarnings("unchecked")
	public CacheSet(int initialCapacity, float loadFactor) {
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Illegal initial capacity: " +
					initialCapacity);
		if (initialCapacity > MAXIMUM_CAPACITY)
			initialCapacity = MAXIMUM_CAPACITY;
		if (loadFactor <= 0 || Float.isNaN(loadFactor))
			throw new IllegalArgumentException("Illegal load factor: " +
					loadFactor);
		
		// Find a power of 2 >= initialCapacity
		int capacity = 1;
		while (capacity < initialCapacity) 
			capacity <<= 1;
		
		this.loadFactor = loadFactor;
		threshold = (int)(capacity * loadFactor);
		table = new Entry[capacity];
	}
	
	/**
	 * Constructs a new set containing the elements in the specified
	 * collection.  The <tt>HashMap</tt> is created with default load factor
	 * (0.75) and an initial capacity sufficient to contain the elements in
	 * the specified collection.
	 *
	 * @param c the collection whose elements are to be placed into this set.
	 * @throws NullPointerException   if the specified collection is null.
	 */
	public CacheSet(Collection<? extends E> c) {
		this(c.size(), .75f);
		addAll(c);
	}
	
	/**
	 * Returns a hash value for the specified integer. 
	 * The shift distances in this function were chosen as the result
	 * of an automated search over the entire four-dimensional search space.
	 */
	private static int hash(int h) {
		h += ~(h << 9);
		h ^=  (h >>> 14);
		h +=  (h << 4);
		h ^=  (h >>> 10);
		return h;
	}
	
	/**
	 * Returns a hash value for the specified object.  In addition to 
	 * the object's own hashCode, this method applies a "supplemental
	 * hash function," which defends against poor quality hash functions.
	 * This is critical because HashMap uses power-of two length 
	 * hash tables.<p>
	 *
	 * The shift distances in this function were chosen as the result
	 * of an automated search over the entire four-dimensional search space.
	 */
	private static int hash(Object x) {
		return hash(x.hashCode());
	}
	
	/**
	 * Returns index for hash code h. 
	 */
	private static int indexFor(int h, int length) {
		return h & (length-1);
	}
	
	/**
	 * Returns the number of elements in this set.
	 * @return #this.elts
	 * @see java.util.Set#size()
	 */
	public int size() {
		return size;
	}
	
	/**
	 * Returns true if this set is empty.
	 * @return no this.elts
	 * @see java.util.Set#isEmpty()
	 */
	public boolean isEmpty() {
		return size==0;
	}
	
	/**
	 * Returns true if this set contains the given element.
	 * @return elt in this.elts
	 * @throws NullPointerException  elt = null
	 * @see java.util.Set#contains(java.lang.Object)
	 */
	public boolean contains(Object elt) {
		Entry<E> e = table[indexFor(hash(elt), table.length)]; 
		while (e != null) {
			if (e.val.equals(elt)) 
				return true;
			e = e.next;
		}
		return false;
	}
	
	/** 
	 * Returns an iterator over the elements in this set.
	 * @return an iterator over this.elts.
	 * @see java.util.Set#iterator()
	 */
	public Iterator<E> iterator() {
		return new SetIterator();
	}
	
	/**
	 * Adds the given element to this set, if not already present.
	 * @ensures this.elts' = this.elts + elt
	 * @throws NullPointerException  elt = null
	 * @return elt !in this.elts
	 */
	public boolean add(E elt) {
		final int i = indexFor(hash(elt), table.length);
		
		for (Entry<E> e = table[i]; e != null; e = e.next) {
			if (e.val.equals(elt)) {
				return false;
			}
		}
		
		table[i] = new Entry<E>(elt, table[i]);
		if (size++ >= threshold)
			resize(2 * table.length);
		
		return true;
	}
	
	/**
	 * Rehashes the contents of this map into a new array with a
	 * larger capacity.  This method is called automatically when the
	 * number of keys in this map reaches its threshold.
	 *
	 * If current capacity is MAXIMUM_CAPACITY, this method does not
	 * resize the map, but sets threshold to Integer.MAX_VALUE.
	 * This has the effect of preventing future calls.
	 *
	 * @param newCapacity the new capacity, MUST be a power of two;
	 *        must be greater than current capacity unless current
	 *        capacity is MAXIMUM_CAPACITY (in which case value
	 *        is irrelevant).
	 */
	@SuppressWarnings("unchecked")
	private void resize(int newCapacity) {
		Entry<E>[] oldTable = table;
		int oldCapacity = oldTable.length;
		if (oldCapacity == MAXIMUM_CAPACITY) {
			threshold = Integer.MAX_VALUE;
			return;
		}
		
		Entry<E>[] newTable = new Entry[newCapacity];
		transfer(newTable);
		table = newTable;
		threshold = (int)(newCapacity * loadFactor);
	}
	
	/** 
	 * Transfer all entries from current table to newTable.
	 */
	private void transfer(Entry<E>[] newTable) {
		Entry<E>[] src = table;
		int newCapacity = newTable.length;
		for (int j = 0; j < src.length; j++) {
			Entry<E> e = src[j];
			if (e != null) {
				src[j] = null;
				do {
					Entry<E> next = e.next;
					int i = indexFor(hash(e.val), newCapacity);  
					e.next = newTable[i];
					newTable[i] = e;
					e = next;
				} while (e != null);
			}
		}
	}
	
	/**
	 * Removes the specified object from this set, if present.
	 * @ensures this.elts' = this.elts - elt
	 * @return elt in this.elts
	 * @throws NullPointerException  elt = null
	 * @see java.util.Set#remove(java.lang.Object)
	 */
	public boolean remove(Object elt) {
		int i = indexFor(hash(elt), table.length);
		Entry<E> prev = table[i];
		Entry<E> e = prev;
		
		while (e != null) {
			Entry<E> next = e.next;
			if (e.val.equals(elt)) {
				size--;
				if (prev == e) 
					table[i] = next;
				else
					prev.next = next;
				return true;
			}
			prev = e;
			e = next;
		}
		
		return false;
		
	}
	
	/**
	 * Returns an iterator over the elements 
	 * whose hashcode() method returns the given hash.
	 * @return an iterator over {e: this.elts | e.hashCode() = hash }
	 */
	public Iterator<E> get(final int hash) {
		final int i = indexFor(hash(hash), table.length);
		return new Iterator<E>() {
			
			Entry<E> current = null, next = table[i];
			
			public boolean hasNext() {
				while(next != null && next.val.hashCode()!=hash) {
					next = next.next;
				}
				return next != null;
			}
			
			public E next() {
				if (!hasNext()) throw new NoSuchElementException();
				current = next;
				next = next.next;
				return current.val;
			}
			
			public void remove() {
				if (current==null)
					throw new IllegalStateException();
				Entry<E> prev = table[i];
				Entry<E> e = prev;
				
				while (e.next != current) {
					prev = e;
					e = e.next;
				}
				
				size--;
				if (prev==e)
					table[i] = next;
				else 
					prev.next = next;
				current = null;
			}
			
		};
	}
	
	/**
	 * Removes all elements from this set.
	 * @ensures no this.elts'
	 * @see java.util.Set#clear()
	 */
	public void clear() {
		for (int i = 0; i < table.length; i++) 
			table[i] = null;
		size = 0;
	}
	
	private static final class Entry<T> {
		Entry<T> next;
		T val;
		
		Entry(T val, Entry<T> next) {
			this.val = val;
			this.next = next;
		}
	}
	
	private final class SetIterator implements Iterator<E> {
		Entry<E> next;	// next entry to return 
		int index;		// current slot 
		Entry<E> current;	// current entry
		
		SetIterator() {
			index = table.length;
			next = null;
			if (size != 0) { // advance to first entry
				while (index > 0 && (next = table[--index]) == null)
					;
			}
		}
		
		public boolean hasNext() {
			return next != null;
		}
		
		public E next() {
			Entry<E> e = next;
			if (e == null) 
				throw new NoSuchElementException();
			
			Entry<E> n = e.next;
			while (n == null && index > 0)
				n = table[--index];
			next = n;
			return (current = e).val;
			
		}
		
		public void remove() {
			if (current == null)
				throw new IllegalStateException();
			
			CacheSet.this.remove(current.val);
			current = null;
		}		
	}
	
}
