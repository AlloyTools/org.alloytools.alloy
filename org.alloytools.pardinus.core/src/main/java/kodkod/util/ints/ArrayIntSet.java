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

import java.util.Arrays;
import java.util.NoSuchElementException;

/**
 * An immutable set of integers, stored in a sorted array.
 * 
 * @specfield ints: set int
 * @author Emina Torlak
 */
public final class ArrayIntSet extends AbstractIntSet {
	private final int[] ints;
	private final int hashcode;
	/**
	 * Constructs a set view for the given array.  The array must contain no duplicates, 
	 * its elements must be sorted
	 * in the ascending order, and its contents
	 * must not be changed while it is in use by this set
	 * @requires all i, j: [0..ints.length) | i < j => array[i] <= array[j]
	 * @ensures this.ints' = ints
	 */
	public ArrayIntSet(int[] ints) {
		this.ints = ints;
		this.hashcode = Ints.superFastHash(ints);
	}
	
	/**
	 * Constructs an ArrayIntSet that is <tt>equal</tt> to the
	 * given set.
	 * @ensures this.ints' = s.ints
	 */
	public ArrayIntSet(IntSet s) {
		this(s.toArray());
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#iterator(int, int)
	 */
	public IntIterator iterator(final int from, final int to) {
		return from <= to ? new AscendingIntArrayIterator(from,to) : new DescendingIntArrayIterator(from,to);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#size()
	 */
	public int size() {
		return ints.length;
	}

	/**
	 * @see kodkod.util.ints.IntSet#ceil(int)
	 */
	public int ceil(int i) {
		final int index = Arrays.binarySearch(ints, i);
		if (index==-ints.length-1) throw new NoSuchElementException();
		else return index >= 0 ? ints[index] : ints[-index-1];
	}

	/**
	 * @see kodkod.util.ints.IntSet#floor(int)
	 */
	public int floor(int i) {
		final int index = Arrays.binarySearch(ints, i);
		if (index==-1) throw new NoSuchElementException();
		else return index >= 0 ? ints[index] : ints[-index-2];
	}

	/**
	 * Returns true if i is in this set.
	 * @return i in this.ints
	 * @see kodkod.util.ints.IntSet#contains(int)
	 */
	public boolean contains(int i) {
		return Arrays.binarySearch(ints, i) >= 0;
	}

	/**
	 * Returns the smallest element in this set.
	 * Throws a NoSuchElementException if this set is empty.
	 * @return min(this.ints)
	 * @throws java.util.NoSuchElementException  no this.ints
	 * @see kodkod.util.ints.IntSet#max()
	 */
	@Override
	public int max() {
		if (ints.length==0) throw new NoSuchElementException();
		return ints[ints.length-1];
	}

	/**
	 * Returns the largest element in this set.
	 * Throws a NoSuchElementException if this set is empty.
	 * @return max(this.ints)
	 * @throws java.util.NoSuchElementException  no this.ints
	 * @see kodkod.util.ints.IntSet#min()
	 */
	@Override
	public int min() {
		if (ints.length==0) throw new NoSuchElementException();
		return ints[0];
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#toArray()
	 */
	@Override
	public int[] toArray() {
		final int[] ret = new int[ints.length];
		System.arraycopy(ints, 0, ret, 0, ints.length);
		return ret;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#toArray(int[])
	 */
	@Override
	public int[] toArray(int[] array) {
		if (array.length < size()) {
			array = new int[ints.length];
		}
		System.arraycopy(ints, 0, array, 0, ints.length);
		return array;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#hashCode()
	 */
	@Override
	public int hashCode() { return hashcode; }
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object o) {
		return (o instanceof ArrayIntSet) ? 
				java.util.Arrays.equals(ints, ((ArrayIntSet)o).ints) : 
				super.equals(o);
	}
	
	/**
	 * An iterator that returns the elements of this int set in the
	 * ascending order.
	 * @author Emina Torlak
	 */
	private final class AscendingIntArrayIterator implements IntIterator {
		private int next, end;
		/**
		 * Constructs a new AscendingIntArrayIterator.
		 * @requires from <= to
		 */
		AscendingIntArrayIterator(int from, int to) {
			final int fromIndex = Arrays.binarySearch(ints, from);
			final int toIndex = Arrays.binarySearch(ints, to);
			next = fromIndex >= 0 ? fromIndex : -fromIndex-1;
			end = toIndex >=0 ? toIndex : -toIndex-2;
		}
		public boolean hasNext() { return next>=0 && next <= end; }
		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			return ints[next++];
		}
		public final void remove() { throw new UnsupportedOperationException(); }
	}
	
	/**
	 * An iterator that returns the elements of this int set in the
	 * descending order.
	 * @author Emina Torlak
	 */
	private final class DescendingIntArrayIterator implements IntIterator  {
		private int next, end;
		/**
		 * Constructs a new AscendingIntArrayIterator.
		 * @requires from >= to
		 */
		DescendingIntArrayIterator(int from, int to) {
			final int fromIndex = Arrays.binarySearch(ints, from);
			final int toIndex = Arrays.binarySearch(ints, to);
			next = fromIndex >= 0 ? fromIndex : -fromIndex-2;
			end = toIndex >=0 ? toIndex : -toIndex-1;
		}
		public boolean hasNext() { return next >= end; }
		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			return ints[next--];
		}
		public final void remove() { throw new UnsupportedOperationException(); }
	}

}
