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

/**
 * A mutable implementation of the <tt>IntVector</tt> interface.  Implements
 * all optional IntVector operations.  In addition to implementing the <tt>IntVector</tt> interface,
 * this class provides methods to manipulate the size of the array that is
 * used internally to store the elements of the IntVector. <p>
 *
 * The <tt>size</tt>, <tt>isEmpty</tt>, <tt>get</tt>, <tt>set</tt>,
 * and <tt>iterator</tt> operations run in constant
 * time.  The <tt>insert</tt> operations run in <i>amortized constant time</i>,
 * that is, adding n elements requires O(n) time.  All of the other operations
 * run in linear time (roughly speaking).  <p>
 *
 * Each <tt>MutableIntVector</tt> instance has a <i>capacity</i>.  The capacity is
 * the size of the array used to store the elements in the list.  It is always
 * at least as large as the list size.  As elements are added to a MutableIntVector,
 * its capacity grows automatically.  The details of the growth policy are not
 * specified beyond the fact that adding an element has constant amortized
 * time cost.<p> 
 *
 * An application can increase the capacity of an <tt>MutableIntVector</tt> instance
 * before adding a large number of elements using the <tt>ensureCapacity</tt>
 * operation.  This may reduce the amount of incremental reallocation.<p>
 * 
 * This impementation is not synchronized and its iterators are not fail-fast.
 * 
 * @author Emina Torlak
 */
public final class ArrayIntVector extends AbstractIntVector {

	private int[] elements;
	private int size;

	/**
	 * Constructs an empty <tt>MutableIntVector</tt> with the specified initial capacity.
	 *
	 * @exception IllegalArgumentException if the specified initial capacity
	 *            is negative
	 */
	public ArrayIntVector(int initialCapacity) {
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Illegal Capacity: "+
					initialCapacity);
		this.elements = new int[initialCapacity];
	}

	/**
	 * Constructs an empty <tt>MutableIntVector</tt> with an initial capacity of ten.
	 */
	public ArrayIntVector() {
		this(10);
	}

	/**
	 * Constructs a <tt>MutableIntVector</tt> containing the elements of the specified
	 * array, in proper sequence.  The <tt>MutableIntVector</tt> instance has an initial capacity of
	 * 110% the size of the specified collection.
	 *
	 * @throws NullPointerException if the specified array is null.
	 */
	public ArrayIntVector(int[] array) {
		size = array.length;
		// Allow 10% room for growth
		int capacity = (int) Math.min((size*110L)/100, Integer.MAX_VALUE);
		elements = new int[capacity];
		System.arraycopy(array, 0, elements, 0, size);
	}

	/**
	 * Trims the capacity of this <tt>MutableIntVector</tt> instance to be the
	 * list's current size.  An application can use this operation to minimize
	 * the storage of an <tt>MutableIntVector</tt> instance.
	 */
	public void trimToSize() {

		int oldCapacity = elements.length;
		if (size < oldCapacity) {
			int[] oldData = elements;
			elements = new int[size];
			System.arraycopy(oldData, 0, elements, 0, size);
		}
	}

	/**
	 * Increases the capacity of this <tt>MutableIntVector</tt> instance, if
	 * necessary, to ensure  that it can hold at least the number of elements
	 * specified by the minimum capacity argument. 
	 */
	public void ensureCapacity(int minCapacity) {

		int oldCapacity = elements.length;
		if (minCapacity > oldCapacity) {
			int[] oldData = elements;
			int newCapacity = (oldCapacity * 3)/2 + 1;
			if (newCapacity < minCapacity)
				newCapacity = minCapacity;
			elements = new int[newCapacity];
			System.arraycopy(oldData, 0, elements, 0, size);
		}
	}
	
	

	/**
	 * @throws IndexOutOfBoundsException  index < 0 or index >= size
	 */
	private void checkExcludeLength(int index) {
		if (index < 0 || index >= size)
			throw new IndexOutOfBoundsException();
	}
	
	/**
	 * @throws IndexOutOfBoundsException  index < 0 or index > size
	 */
	private void checkIncludeLength(int index) {
		if (index < 0 || index > size)
			throw new IndexOutOfBoundsException();
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#get(int)
	 */
	public int get(int index) {
		checkExcludeLength(index);
		return elements[index];
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#size()
	 */
	public int size() {
		return size;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#set(int, int)
	 */
	@Override
	public int set(int index, int element) {
		final int oldValue = get(index);
		elements[index] = element;
		return oldValue;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#add(int)
	 */
	@Override
	public boolean add(int element) {
		ensureCapacity(size+1);
		elements[size++] = element;
		return true;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#add(int, int)
	 */
	@Override
	public void add(int index, int element) {
		checkIncludeLength(index);

		ensureCapacity(size+1); 
		System.arraycopy(elements, index, elements, index + 1, size - index);
		elements[index] = element;
		size++;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntVector#addAll(int, kodkod.util.ints.IntCollection)
	 */
	@Override
	public boolean addAll(int index, IntCollection c) {
		checkIncludeLength(index);
		
		final int csize = c.size();
		if (csize==0) return false;
		
		ensureCapacity(size+csize); 
		System.arraycopy(elements, index, elements, index + csize, size - index);
		
		for(IntIterator iter = c.iterator(); iter.hasNext(); ) {
			elements[index++] = iter.next();
		}
		
		return true;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.AbstractIntVector#removeAt(int)
	 */
	@Override
	public int removeAt(int index) { 
		checkExcludeLength(index);
		final int old = elements[index];
		System.arraycopy(elements, index+1, elements, index, size - index - 1);
		size--;
	   	return old;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.AbstractIntCollection#toArray(int[])
	 */
	@Override
	public int[] toArray(int[] array) {
		if (array.length < size) {
			array = new int[size];
		}
		System.arraycopy(elements, 0, array, 0, size);
		return array;
	}
}
