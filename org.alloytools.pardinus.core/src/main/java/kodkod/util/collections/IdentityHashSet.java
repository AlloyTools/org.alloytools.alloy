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
import java.util.HashSet;
import java.util.Iterator;
import java.util.NoSuchElementException;


/**
 * <p>Implements the <tt>Set</tt> interface with a hash table, using
 * reference-equality in place of object-equality when comparing elements.  
 * In other words, in an <tt>IdentityHashSet</tt>, two elements
 * <tt>e1</tt> and <tt>e2</tt> are considered equal if and only if
 * <tt>(e1==e2)</tt>.  (In normal <tt>Set</tt> implementations (like
 * <tt>Set</tt>) two elements <tt>e1</tt> and <tt>e2</tt> are considered equal
 * if and only if <tt>(e1==null ? e2==null : e1.equals(e2))</tt>.)
 *
 * <p><b>This class is <i>not</i> a general-purpose <tt>Set</tt>
 * implementation!  While this class implements the <tt>Set</tt> interface, it
 * intentionally violates <tt>Set's</tt> general contract, which mandates the
 * use of the <tt>equals</tt> method when comparing objects.  This class is
 * designed for use only in the rare cases wherein reference-equality
 * semantics are required.</b>
 *
 * <p>This class provides all of the optional set operations, and permits
 * <tt>null</tt> elements.  This class makes no
 * guarantees as to the order of the set; in particular, it does not guarantee
 * that the order will remain constant over time.
 *
 * <p>This class provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the system
 * identity hash function ({@link System#identityHashCode(Object)})
 * disperses elements properly among the buckets.
 *
 * <p>This class has one tuning parameter (which affects performance but not
 * semantics): <i>expected maximum size</i>.  This parameter is the maximum
 * number of elements that the set is expected to hold.  Internally,
 * this parameter is used to determine the number of buckets initially
 * comprising the hash table.  The precise relationship between the expected
 * maximum size and the number of buckets is unspecified.
 *
 * <p>If the size of the set sufficiently
 * exceeds the expected maximum size, the number of buckets is increased
 * Increasing the number of buckets ("rehashing") may be fairly expensive, so
 * it pays to create identity hash sets with a sufficiently large expected
 * maximum size.  On the other hand, iteration requires
 * time proportional to the number of buckets in the hash table, so it
 * pays not to set the expected maximum size too high if you are especially
 * concerned with iteration performance or memory usage.
 *
 * <p><b>Note that this implementation is not synchronized.</b>  The iterators 
 * returned by all of this class
 * are <i>not fail-fast</i>:  in the face of concurrent
 * modification, the iterator risks
 * arbitrary, non-deterministic behavior at an undetermined time in the
 * future.
 *
 * <p>Implementation note: This is a simple <i>linear-probe</i> hash table,
 * as described for example in texts by Sedgewick and Knuth.  For many JRE 
 * implementations and operation mixes, this class will yield better performance than
 * {@link HashSet} (which uses <i>chaining</i> rather than linear-probing).
 *
 * @specfield elems: set T
 * @author Emina Torlak
 */
public final class IdentityHashSet<T> extends AbstractSet<T> {
	/* implementation adapted from java.util.IdentityHashMap */
	/**
	 * The minimum capacity, used if a lower value is implicitly specified
	 * by either of the constructors with arguments.  The value 4 corresponds
	 * to an expected maximum size of 2, given a load factor of 2/3.
	 * MUST be a power of two.
	 */
	private static final int MINIMUM_CAPACITY = 4;
	
	/**
	 * The maximum capacity, used if a higher value is implicitly specified
	 * by either of the constructors with arguments.
	 * MUST be a power of two <= 1<<29.
	 */
	private static final int MAXIMUM_CAPACITY = 1 << 29;
	
	/**
	 * Value representing null elements inside tables.
	 */
	private static final Object NULL = new Object();
	
	/**
	 * Use NULL for key if it is null.
	 */
	private static Object maskNull(Object o) {
		return (o == null ? NULL : o);
	}
	
	/**
	 * Return internal representation of null key back to caller as null
	 */
	private static Object unmaskNull(Object o) {
		return (o == NULL ? null : o);
	}
	
	/**
	 * The table, resized as necessary. Length MUST always be a power of two.
	 */
	private Object[] table;
	
	/**
	 * The number of key-value mappings contained in this identity hash map.
	 */
	private int size;
	
	/**
	 * The next size value at which to resize (capacity * load factor).
	 */
	private int threshold;
	
	/**
	 * Constructs a new, empty identity hash map with a default expected
	 * maximum size of 16.
	 * @ensures no this.elems'
	 */
	public IdentityHashSet() {
		this(16);
	}
	
	/**
	 * Constructs a new, empty set with the specified expected maximum size.
	 * Putting more than the expected number of elements into
	 * the set may cause the internal data structure to grow, which may be
	 * somewhat time-consuming.
	 * @ensures no this.elems'
	 * @throws IllegalArgumentException  <tt>expectedMaxSize</tt> < 0
	 */
	public IdentityHashSet(int expectedMaxSize) {
		if (expectedMaxSize < 0)
			throw new IllegalArgumentException("expectedMaxSize < 0: " + expectedMaxSize);
		
		final int initCapacity = capacity(expectedMaxSize);
		threshold = (initCapacity * 2)/3;
		table = new Object[initCapacity];
		size = 0;
	}
	
	/**
	 * Constructs a new identity hash set containing the elements
	 * in the specified collection.
	 * @ensures this.elems' = c.elems
	 * @throws NullPointerException  c = null
	 */
	public IdentityHashSet(Collection<? extends T> c) {
		// Allow for a bit of growth
		this((int) ((1 + c.size()) * 1.1));
		addAll(c);
	}
	
	/**
	 * Returns the appropriate capacity for the specified expected maximum
	 * size.  Returns the smallest power of two between MINIMUM_CAPACITY
	 * and MAXIMUM_CAPACITY, inclusive, that is greater than
	 * (3 * expectedMaxSize)/2, if such a number exists.  Otherwise
	 * returns MAXIMUM_CAPACITY.  If (3 * expectedMaxSize)/2 is negative, it
	 * is assumed that overflow has occurred, and MAXIMUM_CAPACITY is returned.
	 */
	private static int capacity(int expectedMaxSize) {
		// Compute min capacity for expectedMaxSize given a load factor of 2/3
		final int minCapacity = (3 * expectedMaxSize)/2;
		
		// Compute the appropriate capacity
		int result;
		if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
			result = MAXIMUM_CAPACITY;
		} else {
			result = StrictMath.max(MINIMUM_CAPACITY, Integer.highestOneBit(minCapacity));
			if (result < minCapacity) result <<= 1;
		}
		return result;
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public Iterator<T> iterator() {
		return new IdentityIterator();
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public int size() {
		return size;
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public boolean isEmpty() {
		return size==0;
	}
	
	/**
	 * Return index for Object x in a table of size length.
	 */
	private static int hash(Object x, int length) {
		return System.identityHashCode(x) & (length - 1);
	}
	
	/**
	 * Circularly traverse table of size length.
	 **/
	private static int nextKeyIndex(int i, int length) {
		return (i + 3) & (length - 1);
	}
	
	/**
	 * Tests whether the specified object reference is an element in this identity
	 * hash map.
	 * @return o in this.elems
	 */
	@Override
	public boolean contains(Object o) {
		o = maskNull(o);     
		
		for (int i = hash(o, table.length); ; i = nextKeyIndex(i, table.length)) {
			Object item = table[i];
			if (item == o)
				return true;
			if (item == null)
				return false;	            
		}
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public boolean add(T element) {
		final Object o = maskNull(element);
		
		int i = hash(o, table.length);
		
		for(Object item = table[i]; item != null; item = table[i]) {
			if (item == o) return false;
			i = nextKeyIndex(i, table.length);
		}
		
		table[i] = o;
		
		if (++size >= threshold)
			resize(table.length<<1); // newCapacity == 2 * current capacity.
		
		return true;
	}
	
	/**
	 * Resize the table to hold given capacity.  The new capacity must be a 
	 * power of two.
	 */
	private void resize(int newCapacity) {
		final int oldLength = table.length;
		
		if (oldLength == MAXIMUM_CAPACITY)  {// can't expand any further
			if (threshold == MAXIMUM_CAPACITY - 1)
				throw new IllegalStateException("Capacity exhausted.");
			threshold = MAXIMUM_CAPACITY - 1;
			return;
		}
		
		if (oldLength >= newCapacity)
			return;
		
		final Object[] newTable = new Object[newCapacity];
		
		for (int j = 0; j < oldLength; j++) {
			Object o = table[j];
			if (o != null) {
				table[j] = null;
				int i = hash(o, newCapacity);
				while (newTable[i] != null)
					i = nextKeyIndex(i, newCapacity);
				newTable[i] = o;
			}
		}
		
		table = newTable;
		threshold = (newCapacity * 2) / 3;
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public boolean remove(Object o) {
		o = maskNull(o);
		
		for (int i = hash(o, table.length); ; i = nextKeyIndex(i, table.length)) {
			Object item = table[i];
			if (item == o) {
				size--;        
				table[i] = null;
				closeDeletion(i);
				return true;
			}
			if (item == null)
				return false;          
		}
		
	}
	
	/**
	 * Rehash all possibly-colliding entries following a
	 * deletion. This preserves the linear-probe
	 * collision properties required by get, put, etc.
	 *
	 * @param d the index of a newly empty deleted slot
	 */
	private void closeDeletion(int d) {
		// Adapted from Knuth Section 6.4 Algorithm R
		
		// Look for items to swap into newly vacated slot
		// starting at index immediately following deletion,
		// and continuing until a null slot is seen, indicating
		// the end of a run of possibly-colliding keys.
		Object item;
		for (int i = nextKeyIndex(d, table.length); (item = table[i]) != null;
		i = nextKeyIndex(i, table.length) ) {
			// The following test triggers if the item at slot i (which
			// hashes to be at slot r) should take the spot vacated by d.
			// If so, we swap it in, and then continue with d now at the
			// newly vacated i.  This process will terminate when we hit
			// the null slot at the end of this run.
			// The test is messy because we are using a circular table.
			int r = hash(item, table.length);
			if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
				table[d] = item;
				table[i] = null;
				d = i;
			}
		}
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public boolean addAll(Collection<? extends T> c) {
		int n = c.size();
		if (n == 0)
			return false;
		if (n > threshold) // conservatively pre-expand
			resize(capacity(n));
		
		return super.addAll(c);
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public boolean removeAll(Collection<?> c) {
		/* Must revert from AbstractSet's impl to AbstractCollection's, as
		 * the former contains an optimization that results in incorrect
		 * behavior when c is a smaller "normal" (non-identity-based) Set.
		 */
		boolean modified = false;
		Iterator<?> e = iterator();
		while (e.hasNext()) {
			if (c.contains(e.next())) {
				e.remove();
				modified = true;
			}
		}
		return modified;
	}
	
	/**
	 * @inheritDoc
	 */
	@Override
	public void clear() {
		for (int i = 0; i < table.length; i++)
			table[i] = null;
		size = 0;
	}
	
	/**
     * Compares the specified object with this set for equality.  Returns
     * <tt>true</tt> if the given object is also a set and the two sets
     * contain identical object-references.  
     *
     * <p><b>Owing to the reference-equality-based semantics of this set it is
     * possible that the symmetry and transitivity requirements of the
     * <tt>Object.equals</tt> contract may be violated if this set is compared
     * to a normal set.  However, the <tt>Object.equals</tt> contract is
     * guaranteed to hold among <tt>IdentityHashSet</tt> instances.</b>
     * 
     * @return <tt>true</tt> if the specified object is equal to this set.
     * @see Object#equals(Object)
     */
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof IdentityHashSet) {
            final IdentityHashSet<?> s = (IdentityHashSet<?>) o;
            if (s.size() != size) return false;
            final Object[] tab = s.table;
            for (int i = 0; i < tab.length; i++) {
                Object k = tab[i];
                if (k != null && !contains(k))
                    return false;
            }
            return true;
        } else {
            return super.equals(o);  
        }
    }

    /**
     * Returns the hash code value for this set.  The hash code of a set
     * is defined to be the sum of the hashcode of each entry in the set.  
     * This ensures that <tt>t1.equals(t2)</tt> implies
     * that <tt>t1.hashCode()==t2.hashCode()</tt> for any two
     * <tt>IdentityHashSet</tt> instances <tt>t1</tt> and <tt>t2</tt>, as
     * required by the general contract of {@link Object#hashCode()}.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * elements in this set, it is possible that the contractual
     * requirement of <tt>Object.hashCode</tt> mentioned in the previous
     * paragraph will be violated if one of the two objects being compared is
     * an <tt>IdentityHashSet</tt> instance and the other is a normal set.</b>
     *
     * @return the hash code value for this set.
     * @see Object#hashCode()
     * @see Object#equals(Object)
     * @see #equals(Object)
     */
    public int hashCode() {
        int result = 0;
        for (Object o : table) {
            if (o != null) {
                result += System.identityHashCode(unmaskNull(o));
            }
        }
        return result;
    }

	
	/**
	 * An iterator over the elements of an IdentityHashSet.
	 */
	private  final class IdentityIterator implements Iterator<T> {
		int index = (size != 0 ? 0 : table.length); // current slot.
		int lastReturnedIndex = -1;      // to allow remove()
		Object[] traversalTable = table; // reference to main table or copy
		
		public boolean hasNext() {
			for (int i = index; i < traversalTable.length; i++) {
				if (traversalTable[i] != null) {
					index = i;
					return true;
				}
			}
			index = traversalTable.length;
			return false;
		}
		
		@SuppressWarnings("unchecked")
		public T next() {
			if (!hasNext())
				throw new NoSuchElementException();
			
			lastReturnedIndex = index++;
			return (T) unmaskNull(traversalTable[lastReturnedIndex]);
		}
		
		public void remove() {
			if (lastReturnedIndex == -1)
				throw new IllegalStateException();
			
			final int deletedSlot = lastReturnedIndex;
			lastReturnedIndex = -1;
			
			// If traversing a copy, remove in real table.
			// We can skip gap-closure on copy.
			if (traversalTable != IdentityHashSet.this.table) {
				IdentityHashSet.this.remove(traversalTable[deletedSlot]);
				traversalTable[deletedSlot] = null;
			} else { // we are working on the real table...
				// back up index to revisit new contents after deletion
				size--;
				index = deletedSlot;
				
				// Removal code proceeds as in closeDeletion except that
				// it must catch the rare case where an element already
				// seen is swapped into a vacant slot that will be later
				// traversed by this iterator. We cannot allow future
				// next() calls to return it again.  The likelihood of
				// this occurring under 2/3 load factor is very slim, but
				// when it does happen, we must make a copy of the rest of
				// the table to use for the rest of the traversal. Since
				// this can only happen when we are near the end of the table,
				// even in these rare cases, this is not very expensive in
				// time or space.
				final Object[] tab = traversalTable;
				final int length = tab.length;
				
				int d = deletedSlot;
				tab[d] = null;        // vacate the slot
			
				Object item;
				for (int i = nextKeyIndex(d, length); (item = tab[i]) != null; i = nextKeyIndex(i, length)) {
					int r = hash(item, length);
					// See closeDeletion for explanation of this conditional
					if ((i < r && (r <= d || d <= i)) ||
							(r <= d && d <= i)) {
						
						// If we are about to swap an already-seen element
						// into a slot that may later be returned by next(),
						// then clone the rest of table for use in future
						// next() calls. It is OK that our copy will have
						// a gap in the "wrong" place, since it will never
						// be used for searching anyway.					
						if (i < deletedSlot && d >= deletedSlot && traversalTable == IdentityHashSet.this.table) {
							int remaining = length - deletedSlot;
							Object[] newTable = new Object[remaining];
							System.arraycopy(tab, deletedSlot, newTable, 0, remaining);
							traversalTable = newTable;
							index = 0;
						}
						tab[d] = item;
						tab[i] = null;
						d = i;
					}
				}			
			}
		}
		
	}
	
//	public static void main(String[] args) {
//		IdentityHashSet<Integer> s = new IdentityHashSet<Integer>(21);
//		Integer[] elts = new Integer[21];
//		for(int i = 0; i < elts.length; i++) {
//			elts[i] = new Integer(i);
//			s.add(elts[i]);
//		}
//		System.out.println(s);
//		System.out.println(s.size());
//		System.out.println(s.table.length);
//		System.out.println(s.threshold);
//		System.out.println(s.contains(2));
//		System.out.println(s.contains(elts[2]));
//		System.out.println(s.remove(new Integer(0)));
//		System.out.println(s.remove(elts[0]));
//		System.out.println(s);
//		
//		for(Iterator<Integer> iter = s.iterator(); iter.hasNext(); ) {
//			System.out.println(iter.next());
//			iter.remove();
//		}
//		System.out.println(s);
//		
//	}
	
	
}



