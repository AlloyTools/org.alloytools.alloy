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
 * An implementation of the IntTreeSet interface based 
 * on a balanced binary search tree.
 * 
 * @specfield ints: set int
 * @author Emina Torlak
 */
public final class IntTreeSet extends AbstractIntSet implements Cloneable {
	/* The endpoints of the ranges in the tree do not touch, and they are 
	 * sorted by their right endpoints.
	 * @invariant all n: tree.nodes | n.max = n.key && n.min <= n.max && 
	 *              all n': tree.nodes - n | n'.max < n.min - 1 || n'.min > n.max + 1
	 */
	private final IntTree<Range> tree;
	private int size;

	/**
	 * Constructs an empty int set.
	 * @ensures no this.ints'
	 */
	public IntTreeSet() {
		tree = new IntTree<Range>();
		size = 0;
	}

	/**
	 * Constructs a new int set containing the elements
	 * in the specified set.
	 * @ensures this.ints' = s.ints
	 * @throws NullPointerException  s = null
	 */
	public IntTreeSet(IntSet s) {
		this();
		addAll(s);
	}
	
	/**
	 * Copy constructor.
	 * @ensures constructs a deep copy of the original set.
	 */
	private IntTreeSet(IntTreeSet original) {
		this.size = original.size;
		try {
			this.tree = original.tree.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError(); // unreachable code
		}
	}
	
//	public String toString() {
//		for(Range next = tree.min(); next != null; next = tree.successor(next) ) { 
//			System.out.print("[" + next.min + " .. " + next.key+ "] ");
//		}
//		System.out.println("");
//		return "";
//	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#iterator(int,int)
	 */
	public IntIterator iterator(int from, int to) {
		return from <= to ? new AscendingIterator(from, to) : new DescendingIterator(from, to);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#size()
	 */
	public int size() {
		return size;
	}
		
	/**
	 * Returns true if i is in this set.
	 * @return i in this.ints
	 * @see kodkod.util.ints.IntSet#contains(int)
	 */
	@Override
	public boolean contains(int i) {
		final Range r = tree.searchGTE(i);
		return r != null && r.min <= i;
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
		return tree.min().min;
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
		return tree.max().key;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#floor(int)
	 */
	public int floor(int i) {
		checkNonEmpty();
		Range r = tree.searchGTE(i);
		if (r==null || r.min > i) {
			r = tree.searchLTE(i);
			return r == null ? null : r.key;
		} else
			return i;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#ceil(int)
	 */
	public int ceil(int i) {
		checkNonEmpty();
		final Range r = tree.searchGTE(i);
		return r == null ? null : StrictMath.max(i, r.min);
	}
	
	/**
	 * Adds the given integer to this set if not already present
	 * and returns true.  Otherwise does nothing and returns false.
	 * @ensures this.ints' = this.ints + i
	 * @return i in this.ints'
	 * @see kodkod.util.ints.IntSet#add(int)
	 */
	@Override
	public boolean add(int i) {
		final Range ceil = tree.searchGTE(i);
		if (ceil==null || ceil.min > i) {

			final Range floor = tree.searchLTE(i);
			
			if (floor != null && floor.key==i-1) {			
				if (ceil != null && ceil.min==i+1) {
					tree.delete(ceil);
					floor.key = ceil.key;
				} else {
					floor.key = i;
				}
			} else if (ceil != null && ceil.min==i+1) {
				ceil.min = i;
			} else {
				tree.insert(new Range(i,i));
			}
			
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
		final Range ceil = tree.searchGTE(i);
		
		if (ceil != null && i >= ceil.min) {
			if (ceil.min==ceil.key) {
				tree.delete(ceil);
			} else if (i==ceil.min) {
				ceil.min++;
			} else if (i==ceil.key) {
				ceil.key = i-1;
			} else { // split the range in two
				tree.insert(new Range(ceil.min, i-1));
				ceil.min = i+1;
			}
			size--;
			assert size >= 0;
			return true;
		}
		
		return false;		
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.IntSet#containsAll(kodkod.util.ints.IntCollection)
	 */
	@Override
	public boolean containsAll(IntCollection other) {
		if (other instanceof IntTreeSet) {
			IntTreeSet s = (IntTreeSet) other;
			if (size>=s.size) {
				for(Range r1 = s.tree.min(); r1 != null; r1 = s.tree.successor(r1)) {
					Range r0 = tree.searchGTE(r1.key);
					if (r0==null || r1.min < r0.min)
						return false;
				}
				return true;
			}
			return false;
		}
		return super.containsAll(other);
	}
	
	/**
	 * Removes all elements from this set. 
	 * @ensures no this.ints'
	 * @see kodkod.util.ints.IntCollection#clear()
	 */
	@Override
	public void clear() {
		tree.clear();
		size = 0;
	}
	
	/**
	 * Returns a copy of this int tree set.  The copy is independent of this 
	 * IntSet.
	 * @return a copy of this IntSet.
	 * @see kodkod.util.ints.IntSet#clone()
	 */
	@Override
	public IntTreeSet clone() {
		// ok to use copy constructor to clone a final class
		return new IntTreeSet(this);
	}
	
	/**
	 * A range of integers in an int set.
	 * @specfield min: int
	 * @specfield max: int
	 * @invariant min <= max
	 * @invariant max = key
	 * @author Emina Torlak
	 */
	private static final class Range extends IntTree.Node<Range> implements Cloneable {
		private int min;
		
		Range(int min, int max) {
			super(max);
			this.min = min;
		}
		
		protected Range clone() throws CloneNotSupportedException {
			return (Range)super.clone();
		}
		
	}
	
	/**
	 * An iterator that traverses the ints in this set in the 
	 * ascending order.
	 * @author Emina Torlak
	 */
	private final class AscendingIterator implements IntIterator {
		private Range next;
		private final int endpoint;
		private int currentMax, cursor, lastReturned;
		private boolean canRemove;
		
		/**
		 * @requires from <= to
		 */
		AscendingIterator(int from, int to) {
			endpoint = to;
			lastReturned = Integer.MIN_VALUE;
			canRemove = false;
			next = tree.searchGTE(from);
			if (next==null) {
				cursor = 0;
				currentMax = -1;
			} else {
				cursor = StrictMath.max(next.min, from);
				currentMax = next.key;
				next = tree.successor(next);
			}
		}
		
		public boolean hasNext() {
			if (cursor > currentMax) {
				if (next==null) return false;
				this.cursor = next.min;
				this.currentMax = next.key; 
				next = tree.successor(next);
			}
			return lastReturned<Integer.MAX_VALUE && cursor <= endpoint;
		}

		public int next() {
			if (!hasNext())
				throw new NoSuchElementException();
			canRemove = true;
			return lastReturned = cursor++;
		}

		public void remove() {
			if (!canRemove) 
				throw new IllegalStateException();
			IntTreeSet.this.remove((int)lastReturned);
			next = tree.searchGTE((int)cursor);
			canRemove = false;
		}
		
	}
	
	/**
	 * An iterator that traverses the ints in this set in the 
	 * descending order.
	 * @author Emina Torlak
	 */
	private final class DescendingIterator implements IntIterator {
		private Range next;
		private final int endpoint;
		private int currentMin, cursor, lastReturned;
		private boolean canRemove;
		
		/**
		 * @requires from >= to
		 */
		DescendingIterator(int from, int to) {
			endpoint = to;
			lastReturned = Integer.MAX_VALUE;
			canRemove = false;
			next = tree.searchGTE(from);
			if (next==null || next.min > from) {
				next = tree.searchLTE(from);
				if (next==null) {
					cursor = -1;
					currentMin = 0;
				} else {
					cursor = StrictMath.min(next.key, from);
					currentMin = next.min;
				}
			} else {
				cursor = StrictMath.min(next.key, from);
				currentMin = next.min;
			}
		}
		
		public boolean hasNext() {
			if (cursor < currentMin) {
				if (next==null) return false;
				this.cursor = next.key;
				this.currentMin = next.min;
				next = tree.predecessor(next);
			}
			return lastReturned>Integer.MIN_VALUE && cursor >= endpoint;
		}

		public int next() {
			if (!hasNext()) 
				throw new NoSuchElementException();
			canRemove = true;
			return lastReturned = cursor--;
		}

		public void remove() {
			if (!canRemove) 
				throw new IllegalStateException();
			IntTreeSet.this.remove(lastReturned);
			next = tree.searchLTE(cursor);
			canRemove = false;
		}
		
	}
	
	
}
