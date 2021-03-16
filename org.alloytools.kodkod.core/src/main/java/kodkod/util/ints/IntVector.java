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
 * A resizable array of integers.
 *
 * @specfield length: int
 * @specfield elements: [0..size) ->one int
 * @author Emina Torlak
 */
public interface IntVector extends IntCollection {

    /**
     * Returns the number of elements in this vector.
     *
     * @return this.length
     */
    @Override
    public int size();

    /**
     * Returns <tt>true</tt> if this vector contains no elements.
     *
     * @return no this.elements
     */
    @Override
    public boolean isEmpty();

    /**
     * Returns <tt>true</tt> if this vector contains the specified element.
     *
     * @return element in this.elements[int]
     */
    @Override
    public boolean contains(int element);

    /**
     * Returns the element at the specified position in this vector.
     *
     * @return this.elements[index]
     * @throws IndexOutOfBoundsException if the index is out of range (index &lt; 0
     *             || index &gt;= length()).
     */
    public int get(int index);

    /**
     * Returns an iterator over the elements in this vector in proper sequence.
     *
     * @return an iterator over the elements in this vector in proper sequence.
     */
    @Override
    public IntIterator iterator();

    /**
     * Returns an iterator over the elements in this vector in proper sequence,
     * starting <tt>fromIndex<\tt>, inclusive, and ending at <tt>toIndex<\tt>,
     * exclusive. If <tt>fromIndex<\tt> is less than <tt>toIndex<\tt>, then the
     * iterator will return the elements in the descending order.
     *
     * @return an iterator over the elements in this vector in proper sequence,
     *         starting at <tt>fromIndex<\tt>, inclusive, and ending at
     *         <tt>toIndex<\tt>.
     * @throws IndexOutOfBoundsException fromIndex !in [0..this.length) || toIndex
     *             !in [-1..this.length]
     */
    public IntIterator iterator(int fromIndex, int toIndex);

    /**
     * Replaces the element at the specified position in this vector with the
     * specified element, and returns the previous element (optional operation).
     *
     * @ensures this.elements' = this.elements' ++ index -> element
     * @return this.elements[index]
     * @throws UnsupportedOperationException if the <tt>set</tt> method is not
     *             supported by this vector.
     * @throws IllegalArgumentException if some aspect of the specified element
     *             prevents it from being added to this vector.
     * @throws IndexOutOfBoundsException if the index is out of range (index &lt; 0
     *             || index &gt;= length()).
     */
    public int set(int index, int element);

    /**
     * Removes all of the elements from this vector (optional operation). This
     * vector will be empty after this call returns (unless it throws an exception).
     *
     * @ensures this.length' = 0 && no this.elements'
     * @throws UnsupportedOperationException if the <tt>clear</tt> method is not
     *             supported by this vector.
     */
    @Override
    public void clear();

    /**
     * Returns the index in this vector of the first occurrence of the specified
     * element, or -1 if this vector does not contain this element.
     *
     * @return element in this.elements[int] => min(this.elements.element), -1
     */
    public int indexOf(int element);

    /**
     * Returns the index in this vector of the last occurrence of the specified
     * element, or -1 if this vector does not contain this element.
     *
     * @return element in this.elements[int] => max(this.elements.element), -1
     */
    public int lastIndexOf(int element);

    /**
     * Adds the specified element to the end of this vector (optional operation),
     * and returns true if this vector has changed as a result of the call.
     *
     * @ensures this.length' = this.length + 1 && this.elements' = this.elements +
     *          this.length -> element
     * @return this.elements != this.elements'
     * @throws UnsupportedOperationException if the <tt>add</tt> method is not
     *             supported by this vector.
     * @throws IllegalArgumentException if some aspect of this element prevents it
     *             from being added to this vector.
     */
    @Override
    public boolean add(int element);

    /**
     * Inserts the specified element at the specified position in this vector
     * (optional operation), and returns true if this vector has changed as a result
     * of the call. Shifts the element currently at that position (if any) and any
     * subsequent elements to the right (adds one to their indices).
     *
     * @ensures this.length' = this.length + 1 && this.elements' = { i:
     *          [0..this.length'), e: int | i < index => e = this.elements[i], i =
     *          index => e = element, e = this.elements[i-1] }
     * @throws UnsupportedOperationException if the <tt>add</tt> method is not
     *             supported by this vector.
     * @throws IllegalArgumentException if some aspect of the specified element
     *             prevents it from being added to this vector.
     * @throws IndexOutOfBoundsException if the index is out of range (index &lt; 0
     *             || index &gt; length()).
     */
    public void add(int index, int element);

    /**
     * Appends the specified elements to the end of this vector (optional
     * operation), and returns true if this vector has changed as a result of the
     * call.
     *
     * @ensures appends the specified elements to the end of this vector
     * @return this.elements != this.elements'
     * @throws UnsupportedOperationException if the <tt>add</tt> method is not
     *             supported by this vector.
     * @throws IllegalArgumentException if some aspect of an element in the given
     *             vector prevents it from being added to this vector.
     */
    @Override
    public boolean addAll(IntCollection c);

    /**
     * Inserts the specified elements at the specified position in this vector
     * (optional operation), and returns true if this vector has changed as a result
     * of the call. Shifts the element currently at that position (if any) and any
     * subsequent elements to the right.
     *
     * @ensures inserts the specified elements at the specified position in this
     *          vector
     * @return this.elements != this.elements
     * @throws UnsupportedOperationException if the <tt>add</tt> method is not
     *             supported by this vector.
     * @throws IllegalArgumentException if some aspect of an element in the
     *             specified collection prevents it from being added to this vector.
     * @throws IndexOutOfBoundsException if the index is out of range (index &lt; 0
     *             || index &gt; length()).
     */
    public boolean addAll(int index, IntCollection c);

    /**
     * Removes the first occurrence of the given integer from this vector, and
     * returns true if this vector has changed as a result of the call.
     *
     * @ensures removes the first occurrence of the given integer from this vector
     * @return this.elements != this.elements'
     * @throws UnsupportedOperationException this is an unmodifiable collection
     */
    @Override
    public abstract boolean remove(int i);

    /**
     * Removes the element at the specified position in this vector (optional
     * operation). Shifts any subsequent elements to the left (subtracts one from
     * their indices). Returns the element that was removed from the vector.
     *
     * @return this.elements[index]
     * @ensures this.length' = this.length - 1 && this.elements' = { i:
     *          [0..this.length'), e: int | i < index => e = this.elements[i], e =
     *          this.elements[i+1] }
     * @throws UnsupportedOperationException if the <tt>remove</tt> method is not
     *             supported by this vector.
     * @throws IndexOutOfBoundsException if the index is out of range (index &lt; 0
     *             || index &gt;= length()).
     */
    public int removeAt(int index);

    /**
     * Removes all of this vector's elements that are also contained in the
     * specified collection. After this call returns, this collection will contain
     * no elements in common with the specified collection. Returns true if this
     * collection has changed as a result of the call.
     *
     * @ensures removes all of this vector's elements that are also contained in the
     *          specified collection
     * @return this.elements != this.elements'
     * @throws NullPointerException c = null
     * @throws UnsupportedOperationException this is an unmodifiable collection
     */
    @Override
    public abstract boolean removeAll(IntCollection c);

    /**
     * Retains only the elements in this vector that are contained in the specified
     * collection. In other words, removes from this collection all of its elements
     * that are not contained in the specified collection. Returns true if this
     * collection has changed as a result of the call.
     *
     * @ensures retains only the elements in this vector that are contained in the
     *          specified collection
     * @return this.elements != this.elements'
     * @throws NullPointerException c = null
     * @throws UnsupportedOperationException this is an unmodifiable collection
     */
    @Override
    public abstract boolean retainAll(IntCollection c);

    /**
     * Compares the specified object with this vector for equality. Returns
     * <tt>true</tt> if and only if the specified object is also an int vector, both
     * vectors have the same size, and all corresponding pairs of elements in the
     * two vectors are <i>equal</i>.
     *
     * @return <tt>true</tt> if the specified object is equal to this vector.
     */
    @Override
    public boolean equals(Object o);

    /**
     * Returns the hash code value for this vector. The hash code of an int vector
     * is defined to be the {@link Ints#superFastHash(int[])} of the elements in the
     * vector, taken in the ascending order of indices. This ensures that
     * v1.equals(v2) implies that v1.hashCode()==v2.hashCode() for any two
     * IntVectors v1 and v2, as required by the general contract of the
     * Object.hashCode method.
     *
     * @return Ints.superFastHash(this.toArray())
     */
    @Override
    public int hashCode();

    /**
     * Returns an array containing all of the elements in this vector in proper
     * sequence.
     *
     * @return an array containing all of the elements in this vector in proper
     *         sequence.
     */
    @Override
    public int[] toArray();

    /**
     * Copies the components of this vector into the specified array, provided that
     * it is large enough, and returns it. The item at index k in this vector is
     * copied into component k of the given array. If the given array is not large
     * enough, the effect of this method is the same as calling
     * {@linkplain #toArray()}.
     *
     * @ensures array.length>=this.length => all i: [0..this.length) | array'[i] =
     *          this.elements[i]
     * @return array.length>=this.length => array' else this.toArray()
     * @throws NullPointerException array = null
     */
    @Override
    public int[] toArray(int[] array);
}
