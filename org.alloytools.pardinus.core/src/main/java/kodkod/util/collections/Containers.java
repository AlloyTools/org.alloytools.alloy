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
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * Provides utility methods for working with arrays and collections.
 * 
 * @author Emina Torlak
 */
public final class Containers {
	private static Comparator<Object> identityComparator;
	private static Comparator<Object> hashComparator;
	
	private Containers() {}	
	/**
	 * Returns a new iterator over the given array of items.
	 * The iterator is backed by the given array.  The contents
	 * of the array are not modified by the iterator.  The effect
	 * of this method is the same as calling Iterators.iterator(0, items.length, items).
	 * @throws NullPointerException  items = null
	 */
	@SafeVarargs
	public static final <T, E extends T> Iterator<T> iterate(final E... items) {
		return new AscendingArrayIterator<T>(0, items.length, items);
	}
	
	/**
	 * Returns a new iterator over the given array of items.
	 * The iterator is backed by the given array.  The contents
	 * of the array are not modified by the iterator.
	 * The returned iterator enumerates the items located between
	 * indeces start, inclusive, and end, exclusive.  If start < end,
	 * the elements are returned in the ascending order; otherwise,
	 * they are returned in the descending order.
	 * @throws NullPointerException  items = null
	 * @throws IllegalArgumentException  start < end && (start < 0 || end > items.length) ||
	 *                                    start > end && (start >= items.length || end < -1)
	 */
	@SafeVarargs
	public static final <T, E extends T> Iterator<T> iterate(int start, int end, final E... items) {
		if (start < end)
			return new AscendingArrayIterator<T>(start,end,items);
		else if (start > end)
			return new DescendingArrayIterator<T>(start,end,items);
		else 
			return emptyIterator();
	}
	
	/**
	 * Returns an iterator that has no elements.  That is, 
	 * calls to hasNext will return false, and all other
	 * calls will result in a runtime exception.
	 * @return an empty iterator
	 */
	@SuppressWarnings("unchecked")
	public static final <T> Iterator<T> emptyIterator() {
		return (Iterator<T>) Collections.emptySet().iterator();
	}
	
	/**
	 * Calls System.arraycopy(src, srcPos, dest, destPos, length) and returns the destination array.
	 * @ensures System.arraycopy(src, srcPos, dest, destPos, length)
	 * @return dest
	 */
	public static final <T> T[] copy(T[] src, int srcPos, T[] dest, int destPos, int length) { 
		System.arraycopy(src, srcPos, dest, destPos, length);
		return dest;
	}
	
	/**
	 * Calls System.arraycopy(src, 0, dest, 0, src.length) and returns the destination array.
	 * @requires dest.length >= src.length
	 * @ensures System.arraycopy(src, 0, dest, 0, src.length) 
	 * @return dest
	 */
	public static final <T> T[] copy(T[] src, T[] dest) { 
		System.arraycopy(src, 0, dest, 0, src.length);
		return dest;
	}
	
	/**
	 * Returns a comparator that compares objects according to their
	 * {@link System#identityHashCode(Object) identity hashcodes}.
	 * @return a comparator that compares objects according to their 
	 * {@link System#identityHashCode(Object) identity hashcodes}.
	 */
	public static final Comparator<Object> identityComparator() {
		if (identityComparator==null) {
			identityComparator = new Comparator<Object>() {
				public int compare(Object o1, Object o2) {
					final int c1 = System.identityHashCode(o1);
					final int c2 = System.identityHashCode(o2);
					return c1 == c2 ? 0 : (c1 < c2 ? -1 : 1);
				}
			};
		}
		return identityComparator;
	}
	
	/**
	 * Returns 0 if o is null, otherwise returns o.hashCode().
	 * @return  o=null => 0, o.hashCode()
	 */
	static final int hash(Object o) {
		return o==null ? 0 : o.hashCode();
	}
	
	/**
	 * Returns true if both o1 and o2 are null or if o1.equals(o2)
	 * @return true if both o1 and o2 are null or if o1.equals(o2)
	 */
	static final boolean eq(Object o1, Object o2) {
		return o1==null ? o2==null : o1.equals(o2);
	}
	
	/**
	 * Returns a comparator that compares objects according to their
	 * {@link Object#hashCode() hashcodes}.  The null reference is 
	 * considered to have a hashcode of 0.
	 * @return a comparator that compares objects according to their 
	 * {@link Object#hashCode() hashcodes}.
	 */
	public static final Comparator<Object> hashComparator() {
		if (hashComparator==null) {
			hashComparator = new Comparator<Object>() {
				public int compare(Object o1, Object o2) {
					final int c1 = hash(o1);
					final int c2 = hash(o2);
					return c1 == c2 ? 0 : (c1 < c2 ? -1 : 1);
				}
			};
		}
		return hashComparator;
	}
	
	/**
	 * Calls {@link java.util.Arrays#sort(Object[], Comparator)} on the 
	 * given array and returns it.  The elements are sorted in the ascending
	 * order of their identity hashcodes.
	 * @ensures java.util.Arrays.sort(array, {@link #identityComparator()}) 
	 * @return the given array, with its elements sorted in the increasing order of identity hashcodes
	 */
	public static final <T> T[] identitySort(T[] array) {
		java.util.Arrays.sort(array, identityComparator());
		return array;
	}
	
	/**
	 * Calls {@link java.util.Arrays#sort(Object[], Comparator)} on the 
	 * given array and returns it.  The elements are sorted in the ascending
	 * order of their  hashcodes.
	 * @ensures java.util.Arrays.sort(array, {@link #hashComparator()}) 
	 * @return the given array, with its elements sorted in the increasing order of  hashcodes
	 */
	public static final <T> T[] hashSort(T[] array) {
		java.util.Arrays.sort(array, hashComparator());
		return array;
	}
	
	/**
	 * Searches the specified array for the specified object using the binary search algorithm 
	 * and reference equality. 
	 * The array must be sorted into ascending order according to the identity hashcodes of its elements 
	 * (as by {@link #identitySort(Object[])}) prior to making this call. If it is not sorted, 
	 * the results are undefined.  If the array contains multiple occurences of the specified object, 
	 * there is no guarantee which one will be found.
	 * @requires all i, j: [0..array.length) | i < j => array[i].hashCode() <= array[j].hashCode())
	 * @return index of the search key, if it is contained in the array; otherwise, (-(insertion point) - 1). 
	 * The insertion point is defined as the point at which the key would be inserted into the array: the 
	 * index of the first element greater than the key, or array.length, if all elements in the array are less 
	 * than the specified key. Note that this guarantees that the return value will be >= 0 if and only if the 
	 * key is found.
	 */
	public static final int identityBinarySearch(Object[] array, Object key) {
		int low = 0;
		int high = array.length-1;
		int index = System.identityHashCode(key);

		while (low <= high) {
			int mid = (low + high) >>> 1;
			int midIndex = System.identityHashCode(array[mid]);		
			if (midIndex < index)
				low = mid + 1;
			else if (midIndex > index)
				high = mid - 1;
			else { // index found, now check that variables are the same
				if (array[mid]==key) return mid;
				// check all variables with the same index (if any)
				for(int i = mid+1; i < array.length && System.identityHashCode(array[i])==index; i++) {
					if (array[i]==key) return i;
				}
				for(int i = mid-1; i >= 0 && System.identityHashCode(array[i])==index; i--) {
					if (array[i]==key) return i;
				}
				return -(mid+1); // var not found
			}
		}

		return -(low + 1);  // key not found.
	}
	
	/**
	 * Searches the specified array for the specified object using the binary search algorithm 
	 * and object equality. 
	 * The array must be sorted into ascending order according to the hashcodes of its elements 
	 * (as by {@link #hashSort(Object[])}) prior to making this call. If it is not sorted, 
	 * the results are undefined.  If the array contains multiple occurences of the specified object, 
	 * there is no guarantee which one will be found.
	 * @requires all i, j: [0..array.length) | i < j => System.identityHashCode(array[i]) <= System.identityHashCode(array[j])
	 * @return index of the search key, if it is contained in the array; otherwise, (-(insertion point) - 1). 
	 * The insertion point is defined as the point at which the key would be inserted into the array: the 
	 * index of the first element greater than the key, or array.length, if all elements in the array are less 
	 * than the specified key. Note that this guarantees that the return value will be >= 0 if and only if the 
	 * key is found.
	 */
	public static final int hashBinarySearch(Object[] array, Object key) {
		int low = 0;
		int high = array.length-1;
		int index = hash(key);

		while (low <= high) {
			int mid = (low + high) >>> 1;
			int midIndex = hash(array[mid]);		
			if (midIndex < index)
				low = mid + 1;
			else if (midIndex > index)
				high = mid - 1;
			else { // index found, now check that variables are the same
				if (eq(array[mid], key)) return mid;
				// check all variables with the same index (if any)
				for(int i = mid+1; i < array.length && hash(array[i])==index; i++) {
					if (eq(array[i], key)) return i;
				}
				for(int i = mid-1; i >= 0 && hash(array[i])==index; i--) {
					if (eq(array[i], key)) return i;
				}
				return -(mid+1); // var not found
			}
		}

		return -(low + 1);  // key not found.
	}
	
	/**
	 * Returns an identity set backed by the given array (i.e. a set that uses
	 * reference equality for comparisons).
	 * The array must contain no duplicates, its elements must be
	 * sorted in the increasing order of identity hashcodes (as by {@link #identitySort(Object[])}), and its contents
	 * must not be changed while it is in use by the returned set.
	 * @requires all i, j: [0..array.length) | i < j => System.identityHashCode(array[i]) <= System.identityHashCode(array[j])
	 * @return an unmodifiable identity Set view of the given array
	 */
	public static final <T> Set<T> asIdentitySet(final T[] array) {
		return new AbstractSet<T>() {
			public boolean contains(Object o) {
				return identityBinarySearch(array, o) >= 0;
			}
			public Iterator<T> iterator() {	return iterate(array); }
			public int size() { return array.length;	}		
			public int hashCode() {
				int result = 0;
		        for (Object o : array) { result += System.identityHashCode(o); }
		        return result; 
		     }
		};
	}
	
	/**
	 * Returns a set backed by the given array (i.e. a set that uses
	 * object equality for comparisons). 
	 * The array must contain no duplicates, its elements must be
	 * sorted in the increasing order of hashcodes (as by {@link #hashSort(Object[])}), and its contents
	 * must not be changed while it is in use by the returned set.
	 * @requires all i, j: [0..array.length) | i < j => array[i].hashCode() <= array[j].hashCode
	 * @return an unmodifiable Set view of the given array
	 */
	public static final <T> Set<T> asHashSet(final T[] array) {
		return new AbstractSet<T>() {
			public boolean contains(Object o) {
				return hashBinarySearch(array, o) >= 0; 
			}
			public Iterator<T> iterator() { return iterate(array);}
			public int size() { return array.length;}
		};
	}
	
	/**
	 * Returns a new set that contains the asymmetric difference between the left and the right sets.
	 * @return some s: Set<T> | s.elements = left.elements - right.elements
	 */
	public static final <T> Set<T> setDifference(Set<T> left, Set<T> right) { 
		final Set<T> ret = new LinkedHashSet<T>(left);
		ret.removeAll(right);
		return ret;
	}
	
	/**
	 * An unmodifying iterator over an array.
	 */
	private static abstract class ArrayIterator<T> implements Iterator<T> {
		final T[] items;
		final int end;
		int cursor;
		
		/**
		 * Constructs a new iterator over the given array of items.
		 * The iterator is backed by the given array.  The contents
		 * of the array are not modified by the iterator.  The 
		 * constructed iterator returns the items located between the 
		 * indeces start, inclusive, and end, exclusive.
		 * @requires items != null && 
		 *           start < end => end in [0..items.length] && start in [0..end], 
		 *                          start in [0..items.length) && end in [-1..start]
		 */
		@SafeVarargs
		<E extends T> ArrayIterator(int start, int end, final E... items) {
			this.items = items;
			this.cursor = start;
			this.end = end;
		}
		
		public final void remove() {
			throw new UnsupportedOperationException();
		}
	}
	
	/**
	 * An ascending iterator over an array.
	 */
	private static final class AscendingArrayIterator<T> extends ArrayIterator<T> {

		/**
		 * Constructs a new iterator over the given array of items.
		 * @requires items != null && start < end 
		 * @throws IllegalArgumentException  start < 0 || end > items.length
		 */
		<E extends T> AscendingArrayIterator(int start, int end, E[] items) {
			super(start, end, items);
			if (start < 0 || end > items.length) {
				throw new IllegalArgumentException("start < end && (start < 0 || end > items.length)");
			}
		}

		public boolean hasNext() {
			return cursor >= 0 && cursor < end;
		}

		public T next() {
			if (!hasNext()) throw new NoSuchElementException();
			return items[cursor++];
		}	
	}
	
	/**
	 * A descending iterator over an array.
	 */
	private static final class DescendingArrayIterator<T> extends ArrayIterator<T> {
		/**
		 * Constructs a new iterator over the given array of items.
		 * @requires items != null && start > end 
		 * @throws IllegalArgumentException  start >= items.length || end < -1
		 */
		<E extends T> DescendingArrayIterator(int start, int end, E[] items) {
			super(start, end, items);
			if (start >= items.length || end < -1) {
				throw new IllegalArgumentException("start > end && (start >= items.length || end < -1)");
			}
		}

		public boolean hasNext() {
			return cursor > end;
		}

		public T next() {
			if (!hasNext()) throw new NoSuchElementException();
			return items[cursor--];
		}
		
	}

}
