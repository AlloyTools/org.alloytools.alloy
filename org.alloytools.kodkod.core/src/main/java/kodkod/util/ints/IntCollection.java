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
 * The root interface in the int collection hierarchy. A collection 
 * represents a group of integers, known as its elements. Some collections 
 * allow duplicate elements and others do not. Some are ordered and others unordered.
 * Some allow all integers and others only integers in a certain range.
 * 
 * @author Emina Torlak
 */
public interface IntCollection {

	/**
	 * Returns the number of elements in this collection.
	 * @return number of elements in this collection.
	 */
	public abstract int size();
	
	/**
	 * Returns true if this collection has no elements; 
	 * otherwise returns false.
	 * @return true if this collection has no elements, 
	 * false otherwise.
	 */
	public abstract boolean isEmpty();
	
	/**
	 * Returns an iterator over the elements in this collection.
	 * There are no guarantees concerning the order in which the elements
	 * are returned (unless this collection is an instance of some class that provides a guarantee).
	 * @return an iterator over the elements in this collection
	 */
	public abstract IntIterator iterator();
	
	/**
	 * Returns true if i is an element in this collection.
	 * @return true if i is an element in this collection.
	 */
	public abstract boolean contains(int i);
	
	/**
	 * Ensures that this collection contains the given integer, and returns true
	 * if this collection has changed as a result of the call.  
	 * @return true if this collection has changed as a result of the call
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 * @throws IllegalArgumentException  some aspect of the element prevents it 
	 * from being added to this collection.
	 */
	public abstract boolean add(int i);

	/**
	 * Removes a single instance of the given integer from this collection,
	 * and returns true if this collection has changed as a result of the call.
	 * @return true if this collection has changed as a result of the call
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 */
	public abstract boolean remove(int i);
	
	/**
	 * Returns true if this collection contains all of the elements in the specified collection.
	 * @return true if this collection contains all of the elements in the specified collection.
	 * @throws NullPointerException  c = null
	 */
	public abstract boolean containsAll(IntCollection c);
	
	/**
	 * Adds all of the elements in the specified collection to this collection.
	 * Returns true if this collection has changed as a result of the call.
	 * @return true if this collection has changed as a result of the call
	 * @throws NullPointerException  c = null
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 * @throws IllegalArgumentException  some aspect of an element of the specified 
	 * collection prevents it from being added to this collection.
	 */
	public abstract boolean addAll(IntCollection c);
	
	/**
	 * Removes all of this collection's elements that are also contained in the specified 
	 * collection. After this call returns, this collection will contain no elements in 
	 * common with the specified collection. Returns true if this collection has changed as a result of the call. 
	 * @return true if this collection has changed as a result of the call
	 * @throws NullPointerException  c = null
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 */
	public abstract boolean removeAll(IntCollection c);
	
	/**
	 * Retains only the elements in this collection that are contained in the specified 
	 * collection. In other words, removes from this collection all of its elements that 
	 * are not contained in the specified collection.  Returns true if this collection has changed as a result of the call. 
	 * @return rue if this collection has changed as a result of the call
	 * @throws NullPointerException  c = null
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 */
	public abstract boolean retainAll(IntCollection c);
	
	/**
	 * Removes all elements from this collection. 
	 * @throws UnsupportedOperationException  this is an unmodifiable collection
	 */
	public abstract void clear();
	
	/**
     * Returns an array containing all of the elements in this collection.
     * @return an array containing all of the elements in this collection.
     */
	public abstract int[] toArray();
	
	/**
     * Copies the elements of this collection into the specified array, provided
     * that it is large enough, and returns it.  If the array is not large enough,
     * the effect of this method is the same as calling {@linkplain #toArray()}.
     * @return the given array, filled with the elements from this collection, if
     * the it is large enough; otherwise a new array containing all of the elements
     * in this collection.
     * @throws NullPointerException  array = null
     */
    public abstract int[] toArray(int[] array);
}
