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
 * A skeletal implementation of the IntCollection interface.  
 * @author Emina Torlak
 */
public abstract class AbstractIntCollection implements IntCollection {

	/**
	 * Constructs an empty int collection.
	 * @ensures this.isEmpty()
	 */
	protected AbstractIntCollection() {}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#isEmpty()
	 */
	public boolean isEmpty() { return size()==0; }
	
	/**
	 * Iterates through this.ints and returns true if it
	 * finds i, otherwise returns false.
	 * @return true if i is in this collection, otherwise returns false.
	 */
	public boolean contains(int i) {
		for(IntIterator iter = iterator(); iter.hasNext(); ) {
			if (i==iter.next()) return true;
		}
		return false;
	}
	
	/**
	 * Throws an UnsupportedOperationException.
	 * @throws UnsupportedOperationException
	 */
	public boolean add(int i) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Iterates through the elements of this, removes
	 * i if it finds it and returns true.  Otherwise
	 * returns false.  Throws an UnsupportedOperationException
	 * if this.iterator() does not support removal.
	 * @ensures iterates through the elements of this and removes i if it finds it
	 * @return true if this collection has changed as a result of the call 
	 * @throws UnsupportedOperationException  this.iterator() does not support removal
	 */
	public boolean remove(int i) {
		for(IntIterator iter = iterator(); iter.hasNext(); ) {
			if (i==iter.next()) {
				iter.remove();
				return true;
			}
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#containsAll(kodkod.util.ints.IntCollection)
	 */
	public boolean containsAll(IntCollection c) {
		if (size()>=c.size()) {
			for(IntIterator itr = c.iterator(); itr.hasNext(); ) {
				if (!contains(itr.next()))
					return false;
			}
			return true;
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#addAll(kodkod.util.ints.IntCollection)
	 */
	public boolean addAll(IntCollection c) {
		boolean modified = false;
		for(IntIterator itr = c.iterator(); itr.hasNext(); ) {
			if (add(itr.next()))
				modified = true;
		}
		return modified;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#retainAll(kodkod.util.ints.IntCollection)
	 */
	public boolean retainAll(IntCollection c) {
		boolean modified = false;
		for(IntIterator itr = iterator(); itr.hasNext(); ) {
			if (!c.contains(itr.next())) {
				modified = true;
				itr.remove();
			}
		}
		return modified;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#removeAll(kodkod.util.ints.IntCollection)
	 */
	public boolean removeAll(IntCollection c) {
		boolean modified = false;
		for(IntIterator itr = iterator(); itr.hasNext();) {
			if (c.contains(itr.next())) {
				modified = true;
				itr.remove();
			}
		}
		return modified;
	}

	 /**
     * This implementation iterates over this set, removing each
     * element using the <tt>Iterator.remove</tt> operation.  Most
     * implementations will probably choose to override this method for
     * efficiency.<p>
     *
     * Note that this implementation will throw an
     * <tt>UnsupportedOperationException</tt> if the iterator returned by this
     * collection's <tt>iterator</tt> method does not implement the
     * <tt>remove</tt> method and this collection is non-empty.
     *
     * @throws UnsupportedOperationException if the <tt>clear</tt> method is
     * 		  not supported by this collection.
     */
	public void clear() {
		for(IntIterator itr = iterator(); itr.hasNext();) {
			itr.next();
			itr.remove();
		}
	}
	
	/**
	 * Returns the result of calling {@linkplain #toArray(int[])} with
	 * a freshly constructed array of length this.size().
	 * @return this.toArray(new int[size()])
	 * @see kodkod.util.ints.IntCollection#toArray()
	 */
	public int[] toArray() { return toArray(new int[size()]); }
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#toArray(int[])
	 */
	public int[] toArray(int[] array) {
		if (array.length < size()) {
			array = new int[size()];
		}
		int i = 0;
		for(IntIterator itr = iterator(); itr.hasNext(); ) {
			array[i++] = itr.next();
		}
		return array;
	}
}
