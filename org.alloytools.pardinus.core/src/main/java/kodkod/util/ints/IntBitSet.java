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
 * An implementation of the IntSet interface based on a bit map. 
 * An IntBitSet can store only numbers in the half-open range
 * [0..capacity) where capacity is a user-specified value.  
 * The implementation will allocated enough bits to explicitly represent all allowed
 * integers; it performs better than a tree set when the stored integers
 * are not clustered.
 * @specfield capacity: [0..Integer.MAX_VALUE]
 * @invariant all i: this.ints | 0 <= i < capacity
 * @author Emina Torlak
 */
public final class IntBitSet extends AbstractIntSet implements Cloneable {
	// implementation adapted from java.util.JumboEnumSet
	private final int capacity;
	/*
     * Bit vector representation of this set.  The ith bit of the jth
     * element of this array represents the  presence of universe[64*j +i]
     * in this set.
     */
    private long elements[];

    // Redundant - maintained for performance
    private int size;
	
	/**
	 * Constructs an empty IntBitSet that can store up
	 * to capacity elements.
	 * @ensures no this.ints' && this.capacity' = capacity
	 * @throws IllegalArgumentException  capacity < 0
	 */
	public IntBitSet(int capacity) {
		if (capacity < 0) throw new IllegalArgumentException("capacity < 0");
		this.capacity = capacity;
		elements = new long[(capacity >>> 6) + 1];
		size = 0;
	}
	
	/**
	 * Constructs an IntBitSet that can store up to capacity elements.
	 * The set is initialized to contain all integers i such that 
	 * data[i>>>6] & (1L<<i) == 1.  This IntBitSet is backed by the given
	 * data array.  The array must not be modified while in use by this set.
	 * @requires 0 <= capacity < max({i: int | data[i>>>6] & (1L<<i) == 1}) or (capacity>>>6)+1 > data.length
	 * @throws IllegalArgumentException  capacity is out of range
	 */
	public IntBitSet(int capacity, long[] data) {
		if (capacity > (data.length<<6)) throw new IllegalArgumentException("capacity too large: " + capacity + ", max: " + (data.length<<6));
		this.capacity = capacity;
		this.elements = data;
		recalculateSize();
		
//		System.out.println("capacity: " + capacity + ", max: " + max() + ", data.length: " + data.length);
//		System.out.println(Arrays.toString(data));
		if (size > 0 && capacity <= max())  throw new IllegalArgumentException("capacity too small");
	}
	
	/**
	 * Returns the smallest element in this set.
	 * Throws a NoSuchElementException if this set is empty.
	 * @return min(this.ints)
	 * @throws java.util.NoSuchElementException  no this.ints
	 * @see kodkod.util.ints.IntSet#min()
	 */
	@Override
	public int min() {
		checkNonEmpty();
		int minWordIndex = 0;
		while(elements[minWordIndex]==0) { minWordIndex++; }
		return (minWordIndex << 6) + Long.numberOfTrailingZeros(elements[minWordIndex]);
	}

	/**
	 * Returns the largest element in this set.
	 * Throws a NoSuchElementException if this set is empty.
	 * @return max(this.ints)
	 * @throws java.util.NoSuchElementException  no this.ints
	 * @see kodkod.util.ints.IntSet#max()
	 */
	@Override
	public int max() {
		checkNonEmpty();
		int maxWordIndex = elements.length-1;
		while(elements[maxWordIndex]==0) { maxWordIndex--; }
		return (maxWordIndex << 6) + 63 - Long.numberOfLeadingZeros(elements[maxWordIndex]);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#ceil(int)
	 */
	public int ceil(int i) {
		if (i <= 0)
			return min();
		int wordIndex = wordIndex(i);
		long word = 0;
		if (wordIndex < elements.length) {
			word = (extendedMask(i) & elements[wordIndex]);
		}
		while(word==0 && wordIndex < elements.length-1) {
			word = elements[++wordIndex];
		}
		if (word==0)
			throw new NoSuchElementException();
		else 
			return (wordIndex << 6) + Long.numberOfTrailingZeros(word);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#floor(int)
	 */
	public int floor(int i) {
		if (i < 0)
			throw new NoSuchElementException();
		int wordIndex = wordIndex(i);
		long word = 0;
		if (wordIndex < elements.length) {
			word = ((~extendedMask(i+1)) & elements[wordIndex]);
		} else {
			wordIndex = elements.length-1;
			word = elements[wordIndex];
		}
		while(word==0 && wordIndex > 0) {
			word = elements[--wordIndex];
		}
		if (word==0)
			throw new NoSuchElementException();
		else 
			return (wordIndex << 6) + 63 - Long.numberOfLeadingZeros(word);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#iterator()
	 */
	@Override
	public IntIterator iterator() {
		return new AscendingIterator(0,capacity);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#iterator(int, int)
	 */
	public IntIterator iterator(int from, int to) {
		return from > to ? new DescendingIterator(from,to) : new AscendingIterator(from,to);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#size()
	 */
	public int size() {
		return size;
	}
	
	/**
	 * Returns the capacity of this int bit set
	 * @return this.capacity
	 */
	public int capacity() { return capacity; }
		
	/**
	 * Returns the index of the word that contains
	 * the bit that represents the integer i.
	 * @requires 0 <= i < this.capacity
	 */
	private final int wordIndex(int i) {
		return i >>> 6;
	}
	
	/**
	 * Returns a bit mask that has 1 in the position representing the
	 * given integer within its word (obtained by wordIndex(i))
	 * @requires 0 <= i < this.capacity
	 */
	private final long bitMask(int i) {
		return 1L << i;
	}
	
	/**
	 * Returns a bit mask that has 1 at every index greater than
	 * or equal to the position representing the
	 * given integer within its word. 
	 * @requires 0 <= i < this.capacity
	 */
	private final long extendedMask(int i) {
		return -1L << i;
	}
	
	/**
	 * @return i in [0..this.capacity)
	 */
	private final boolean allows(int i) {
		return 0 <= i && i < capacity;
	}
	
	/**
	 * Returns true if i is in this set.
	 * @return i in this.ints
	 * @see kodkod.util.ints.IntSet#contains(int)
	 */
	@Override
	public boolean contains(int i) {
		return allows(i) && (elements[wordIndex(i)] & (bitMask(i))) != 0;
	}

	/**
	 * Adds the given integer to this set if not already present
	 * and returns true.  Otherwise does nothing and returns false.
	 * @ensures this.ints' = this.ints + i
	 * @return i in this.ints'
	 * @throws IllegalArgumentException  i !in [0..this.capacity)
	 * @see kodkod.util.ints.IntSet#add(int)
	 */
	@Override
	public boolean add(int i) {
		if (!allows(i)) throw new IllegalArgumentException(i + " !in [0.." + capacity + ")");
		
		final int wordIndex = wordIndex(i);
        final long oldElements = elements[wordIndex];
        elements[wordIndex] |= bitMask(i);
        if (elements[wordIndex] != oldElements) {
        		size++;
        		return true;
        }
        return false;
	}

	/**
	 * Removes the given integer from this set if already present and
	 * returns true.  Otherwise does nothing and returns false.
	 * @ensures this.ints' = this.ints - i
	 * @return i !in this.ints'
	 * @see kodkod.util.ints.IntSet#remove(int)
	 */
	@Override
 	public boolean remove(int i) {
		if (allows(i)) {			
			final int wordIndex = wordIndex(i);
	        final long oldElements = elements[wordIndex];
	        elements[wordIndex] &= ~bitMask(i);
	        if (elements[wordIndex] != oldElements) {
	        		size--;
	        		return true;
	        }
		}
        
        return false;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntCollection#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return size==0;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#containsAll(kodkod.util.ints.IntCollection)
	 */
	@Override
	public boolean containsAll(IntCollection other) {
		if (other instanceof IntBitSet) {
			final IntBitSet s = (IntBitSet) other;
			if (isEmpty() || s.isEmpty()) return isEmpty() ? s.isEmpty():true;
			if (size < s.size || max() < s.max()) return false;
			final int minLength = StrictMath.min(elements.length, s.elements.length);
			for(int wordIndex = 0; wordIndex < minLength; wordIndex++) {
				if ((s.elements[wordIndex] & ~elements[wordIndex]) != 0)
					return false;
			}
			return true;
		}
		return super.containsAll(other);
	}
	 
	/**
     * Recalculates the size and returns true if the size has changed.
     */
    private boolean recalculateSize() {
        final int oldSize = size;
        size = 0;
        for(long elt: elements) {
        		size += Long.bitCount(elt);
        }
        return size!=oldSize;
    }
    
   /**
    * {@inheritDoc}
    * @see kodkod.util.ints.IntSet#addAll(kodkod.util.ints.IntCollection)
    */
    @Override
	public boolean addAll(IntCollection other) {
		if (other instanceof IntBitSet) {
			final IntBitSet s = (IntBitSet) other;
			if (s.isEmpty()) return false;
			if (s.max() >= capacity) 
				throw new IllegalArgumentException(s.max()+" !in [0.." + capacity + ")");
			final int minLength = StrictMath.min(elements.length, s.elements.length);
			for(int wordIndex = 0; wordIndex < minLength; wordIndex++) {
				elements[wordIndex] |= s.elements[wordIndex];
			}
			return recalculateSize();
		}
		return super.addAll(other);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#retainAll(kodkod.util.ints.IntCollection)
	 */
	@Override
	public boolean retainAll(IntCollection other) {
		if (other instanceof IntBitSet) {
			final IntBitSet s = (IntBitSet) other;
			final int minLength = StrictMath.min(elements.length, s.elements.length);
			int wordIndex = 0;
			for(; wordIndex < minLength; wordIndex++) {
				elements[wordIndex] &= s.elements[wordIndex];
			}
			for(; wordIndex < elements.length; wordIndex++) {
				elements[wordIndex] = 0;
			}
			return recalculateSize();
		}
		return super.retainAll(other);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#removeAll(kodkod.util.ints.IntCollection)
	 */
	@Override
	public boolean removeAll(IntCollection other) {
		if (other instanceof IntBitSet) {
			final IntBitSet s = (IntBitSet) other;
			final int minLength = StrictMath.min(elements.length, s.elements.length);
			for(int wordIndex = 0; wordIndex < minLength; wordIndex++) {
				elements[wordIndex] &= ~s.elements[wordIndex];
			}
			return recalculateSize();
		}
		return super.removeAll(other);
	}

	/**
	 * Removes all elements from this set. 
	 * @ensures no this.ints'
	 * @see kodkod.util.ints.IntCollection#clear()
	 */
	@Override
	public void clear() {
		Arrays.fill(elements, 0);
        size = 0;
	}

	/**
	 * Returns a copy of this int bit set.  The copy is independent of this 
	 * IntSet.
	 * @return a copy of this IntSet.
	 * @see kodkod.util.ints.IntSet#clone()
	 */
	@Override
	public IntBitSet clone() {
		try {
			final IntBitSet ret = (IntBitSet) super.clone();
			ret.elements = (long[]) this.elements.clone();
			return ret;
		} catch (CloneNotSupportedException e) {
			throw new InternalError(); // unreachable code
		}
		
	}
	
	/**
	 * Stores common fields and methods for the ascending and descending iterators.
	 */
	private abstract class AbstractIterator implements IntIterator {
		long unseen;
        int unseenIndex, lastReturned;
        
		public void remove() {
			if (lastReturned < 0)
                throw new IllegalStateException();
            elements[wordIndex(lastReturned)] -= bitMask(lastReturned);
            size--;
            lastReturned = -1;
		}	
	}
	
	/**
	 * Implementation of an ascending iterator over (a subset of) this set.
	 */
	private final class AscendingIterator extends AbstractIterator {
		private final long maxMask;
		private final int maxIndex;
        
        /**
		 * Constructs an ascending iterator that returns elements between
		 * from and to.  
		 * @requires from <= to 
		 */
        AscendingIterator(int from, int to) {
        		if (from >= capacity || to < 0) {
        			unseenIndex = maxIndex = elements.length;
        			unseen = maxMask = 0L;
        		} else {
        			if (to >= capacity) {
        				maxIndex = elements.length - 1;
        				maxMask = -1L;
        			} else {
        				maxIndex = wordIndex(to);
        				maxMask = (bitMask(to)==Long.MIN_VALUE ? -1L : ~extendedMask(to+1));
        			}
        			if (from < 0) {
        				unseenIndex = 0;
        				unseen = elements[0];
        			} else {
        				unseenIndex = wordIndex(from);
        				unseen = elements[unseenIndex] & extendedMask(from);
        			}
        			
        		}
            lastReturned = -1;
        }
        
        public boolean hasNext() {
            while (unseen == 0 && unseenIndex < elements.length - 1)
                unseen = elements[++unseenIndex];
            return (unseenIndex < maxIndex && unseen != 0) ||
                   (unseenIndex == maxIndex && (unseen & maxMask) != 0);
        }

		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			final long lastReturnedMask = Long.lowestOneBit(unseen);
            	unseen -= lastReturnedMask;
            	lastReturned = (unseenIndex << 6) + Long.numberOfTrailingZeros(lastReturnedMask);
            	return lastReturned;
		}

	}
	
	/**
	 * Implementation of a descending iterator over (a subset of) this set.
	 */
	private final class DescendingIterator extends AbstractIterator {
		private final long minMask;
		private final int minIndex;
          
        /**
		 * Constructs a descending iterator that returns elements between
		 * from and to.  
		 * @requires from >= to 
		 */
        DescendingIterator(int from, int to) {
        		if (to >= capacity || from < 0) {
        			unseenIndex = minIndex = 0;
        			unseen = minMask = 0L;
        		} else {
        			if (from < capacity) {
        				unseenIndex = wordIndex(from);
            			unseen = elements[unseenIndex] & 
            			         (bitMask(from)==Long.MIN_VALUE ? -1L : ~extendedMask(from+1));	
        			} else {
        				unseenIndex = elements.length-1;
            			unseen = elements[unseenIndex];
        			}
        			if (to < 0) {
        				minIndex = 0 ;
            			minMask = -1L;
        			} else {
        				minIndex = wordIndex(to);
            			minMask = extendedMask(to);
        			}
        		}
            lastReturned = -1;
        }
        
        public boolean hasNext() {
            while (unseen == 0 && unseenIndex > 0)
                unseen = elements[--unseenIndex];
            return (unseenIndex > minIndex && unseen != 0) ||
                   (unseenIndex == minIndex && (unseen & minMask) != 0);
        }

		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			final long lastReturnedMask = Long.highestOneBit(unseen);
            	unseen -= lastReturnedMask;
            	lastReturned = (unseenIndex << 6) + 63 - Long.numberOfLeadingZeros(lastReturnedMask);
            	return lastReturned;
		}
	}
	
}
