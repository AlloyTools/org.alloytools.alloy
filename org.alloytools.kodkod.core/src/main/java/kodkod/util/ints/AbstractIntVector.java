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
 * A skeletal implementation of the IntVector interface.   
 *
 * 
 * @specfield length: int
 * @specfield elements: [0..size) ->one int
 * 
 * @author Emina Torlak
 */
public abstract class AbstractIntVector extends AbstractIntCollection implements IntVector {
	
	/**
	 * Constructs an empty int vector.
	 * @ensures no this.elements'
	 */
	protected AbstractIntVector() {}

    /**
     * {@inheritDoc}
     * @see kodkod.util.ints.IntVector#contains(int)
     */
    public boolean contains(int element) {
    	for(int i = 0, max = size(); i < max; i++) {
    		if (get(i)==element) return true;
    	}
    	return false;
    }
	
    /**
     * Throws {@link UnsupportedOperationException}.
     * @see kodkod.util.ints.IntVector#set(int,int)
     */
    public int set(int index, int element) {
    	throw new UnsupportedOperationException();
    }
    
    /**
     * {@inheritDoc}
     * @see kodkod.util.ints.IntVector#indexOf(int)
     */
    public int indexOf(int element) {
    	for(int i = 0, length=size(); i < length; i++) {
			if (get(i)==element) return i;
		}
		return -1;
    }

   /**
    * {@inheritDoc}
    * @see kodkod.util.ints.IntVector#lastIndexOf(int)
    */
    public int lastIndexOf(int element) {
    	for(int i = size()-1; i >= 0; i--) {
			if (get(i)==element) return i;
		}
		return -1;
    }
    
    /**
     * Calls this.add(this.size(), element)
     * @see kodkod.util.ints.IntVector#add(int)
     * @see kodkod.util.ints.IntVector#add(int,int)
     */
    public boolean add(int element) { 
    	final int length = size();
    	add(length,element);
    	return length != size();
    }
        
   /**
    * Throws {@link UnsupportedOperationException}
    * @see kodkod.util.ints.IntVector#add(int, int)
    */
    public void add(int index, int element) { throw new UnsupportedOperationException(); }
    
    /**
     * Returns the result of calling {@linkplain #addAll(int, IntCollection) this.addAll(size(), c)}.
     * @return this.addAll(size(), c)
     * @see kodkod.util.ints.AbstractIntCollection#addAll(kodkod.util.ints.IntCollection)
     */
    public boolean addAll(IntCollection c) {
    	return addAll(size(), c);
    }
    
    /**
     * Throws an UnsupportedOperationException.
     * @see kodkod.util.ints.IntVector#addAll(int, kodkod.util.ints.IntCollection)
     */
    public boolean addAll(int index, IntCollection c) { throw new UnsupportedOperationException(); }
    
    /**
     * Throws an UnsupportedOperationException.
     * @see kodkod.util.ints.IntVector#removeAt(int)
     */
    public int removeAt(int index) { 
    	throw new UnsupportedOperationException();
    }
       
    /**
     * Calls this.iterator(0, length())
     * @see kodkod.util.ints.IntVector#iterator()
     * @see kodkod.util.ints.IntVector#iterator(int,int)
     */
    public IntIterator iterator() {
    	return iterator(0, size());
    }
    
    /**
     * {@inheritDoc}
     * @see kodkod.util.ints.IntVector#iterator(int, int)
     */
    public IntIterator iterator(int fromIndex, int toIndex) {
    	return fromIndex<=toIndex ? new AscendingIntVectorIterator(fromIndex,toIndex) : 
			new DescendingIntVectorIterator(fromIndex,toIndex);
    }
       
    /**
     * Returns the hash code value for this vector.  
     *
     * @return the hash code value for this vector.
     * @see Object#hashCode()
     * @see Object#equals(Object)
     * @see #equals(Object)
     */
	public int hashCode() {
		final int length = size();
		int hash = length;
		for(int i = 0; i < length; i++) {
			hash = Ints.superFastHashIncremental(get(i), hash);
		}
		return Ints.superFastHashAvalanche(hash);
 	}

	/**
     * Compares the specified object with this vector for equality.  Returns
     * <tt>true</tt> if and only if the specified object is also an int vector, both
     * vectors have the same size, and all corresponding pairs of elements in
     * the two vectors are <i>equal</i>.  
     * 
     * @return <tt>true</tt> if the specified object is equal to this vector.
     */
	public boolean equals(Object o) {
		if (o==this) return true;
		if (o instanceof IntVector) {
			final IntVector l = (IntVector) o;
			final int length = size();
			if (l.size()==length) {
				for (int i = 0; i < length; i++) {
					if (get(i) != l.get(i)) return false;
				}
				return true;
			}
		}
		return false;
	}
	
	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuilder buf = new StringBuilder();
		buf.append("[");
		IntIterator itr = iterator();
		if (itr.hasNext()) buf.append(itr.next());
		while(itr.hasNext()) {
			buf.append(", ");
			buf.append(itr.next());
		}
		buf.append("]");
		return buf.toString();
	}

    
    private abstract class IntVectorIterator implements IntIterator {
		int next, end, last;
		IntVectorIterator(int fromIndex, int toIndex) {
			next = fromIndex;
			end = toIndex;
			last = -1;
		}
		public final void remove() {
			if (last < 0) throw new IllegalStateException();
			AbstractIntVector.this.removeAt(last);
			next = last;
			last = -1;
		}
	}
	
	private final class AscendingIntVectorIterator extends IntVectorIterator {
		/**
		 * Constructs a new AscendingIntArrayIterator.
		 * @requires fromIndex <= toIndex
		 */
		AscendingIntVectorIterator(int fromIndex, int toIndex) {
			super(fromIndex, toIndex);
		}
		public boolean hasNext() { return last<Integer.MAX_VALUE && next < end; }
		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			last = next++;
			return get(last);
		}
	}
	
	private final class DescendingIntVectorIterator extends IntVectorIterator {
		/**
		 * Constructs a new AscendingIntArrayIterator.
		 * @requires fromIndex >= toIndex
		 */
		DescendingIntVectorIterator(int fromIndex, int toIndex) {
			super(fromIndex, toIndex);
		}
		public boolean hasNext() { return next > end; }
		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			last = next--;
			return get(last);
		}
	}
}
