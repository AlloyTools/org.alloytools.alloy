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

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * <p>A tree-based sparse sequence implementation.  Unlike {@link kodkod.util.ints.TreeSequence},
 * <b>this is not a general-purpose sparse sequence implementation</b>.  In particular,
 * the entries with consecutive indices and the same value are not stored explicitly.  As a result, 
 * methods
 * that return an {@link kodkod.util.ints.IndexedEntry} may re-use the same object.  
 * Specifically, the last assertion in the following code snippet may fail.</p>
 * <pre>
 * // let s be a range sequence abstractly represented as { 0->v, 1->v, 2->v }
 * IndexedEntry<V> e1 = s.predecessor(2);
 * assert e1.index()==1; // this will work
 * IndexedEntry<V> e2 = s.predecessor(1);
 * assert e1.index()==1; // this may fail, as e1 may be == to e2
 * </pre>  
 * <p>The entries returned by this implementation's {@link #iterator()} are unique
 * to that iterator (but not necessarily independent of each other).  For example, </p>
 * <pre>
 * // let s be a range sequence abstractly represented as { 0->v, 1->v, 2->v }
 * Iterator<IndexedEntry<V>> iter1 = s.iterator();
 * IndexedEntry<V> e1 = iter1.next();
 * assert e1.index()==0; // this will work
 * iter1.next();
 * assert e1.index()==0; // this may fail, as the previous call may have changed the state of e1
 * Iterator<IndexedEntry<V>> iter2 = s.iterator();
 * IndexedEntry<V> e2 = iter2.next();
 * iter1.next();
 * assert e2.index()==0; // this will work
 * </pre>  
 * <p>This implementation is a good choice when the client expects the usage pattern with many consecutive
 * indices mapped to the same value, and when there is no need for entry uniqueness.  </p>
 * @author Emina Torlak
 */
public final class RangeSequence<V> extends AbstractSparseSequence<V> implements Cloneable {
	/* The ranges are sorted by their right endpoints.  All consecutive indices
	 * that map to the same value are represented by a single range node.  
	 * @invariant (all n: tree.nodes | n.max = n.key && n.min <= n.max) && 
	 *            (no disj n, n': tree.nodes | n.value=n'.value && n.max = n'.min-1)
	 */
	private final IntTree<Entry<V>> tree;
	private final EntryView<V> view;
	private int size;
	
	/**
	 * Constructs an empty RangeSequence. 
	 * @ensures no this.entries'
	 */
	public RangeSequence() {
		view = new EntryView<V>(Integer.MIN_VALUE,null);
		tree = new IntTree<Entry<V>>();
		size = 0;
	}

	/**
	 * Copy constructor.
	 * @ensures creatres a deep copy of the original
	 */
	private RangeSequence(RangeSequence<V> original) {
		this.size = original.size;
		try {
			this.tree = original.tree.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError(); // unreachable code;
		}
		view = new EntryView<V>(Integer.MIN_VALUE,null);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#iterator(int, int)
	 */
	public Iterator<IndexedEntry<V>> iterator(int from, int to) {
		return from <= to ? new AscendingIterator(from, to) : new DescendingIterator(from, to);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#size()
	 */
	public int size() {
		return size;
	}

	/**
	 * Removes all entries from this sequences.
	 * @ensures no this.entries'
	 * @see kodkod.util.ints.SparseSequence#clear()
	 */
	public void clear() {
		tree.clear();
		size = 0;
	}

	/**
	 * Returns true if e is the head of a contiguous homogenous
	 * sequence starting with the mapping e.min->e.value and 
	 * ending with the mapping index->value.
	 * @return e!=null index-1 = e.key && equal(value, e.value) 
	 */
	private boolean isHeadOf(Entry<V> e, int index, V value){
		return e!=null && e.key==index-1 && equal(e.value, value);
	}
	
	/**
	 * Returns true if e is the tail of a contiguous homogenous
	 * sequence starting with the mapping index->value and 
	 * ending with the mapping e.max->e.value.
	 * @return e!=null && index+1 = e.min && equal(value, e.value) 
	 */
	private boolean isTailOf(Entry<V> e, int index, V value) {
		return e!=null && e.min()==index+1 && equal(e.value, value);
	}
	
	
	/**
	 * Merges the mapping index->value into its floor or ceiling, if 
	 * possible.  Otherwise creates a new node for index->value and
	 * inserts into the tree.
	 * @requires index !in this.nodes.key
	 * @requires f = searchLTE(index) && c = searchGTE(index)
	 * @ensures this.entries' = this.entries + index->value
	 */
	private void merge(int index, V value, Entry<V> f, Entry<V> c) {
		if (isHeadOf(f, index, value)) {
			if (f.isPoint()) {
				if (isTailOf(c, index, value)) {
					if (c.isPoint()) { // [f: 0->a][i: 1->a][c: 2->a] ---> [{0,1,2}->a]
						tree.delete(c);
						tree.replace(f, new Range<V>(f.key, c.key, value));
					} else { // [f: 0->a][i: 1->a][c: {2,3}->a] ---> [c: {0,1,2,3}->a]
						tree.delete(f);
						((Range<V>)c).min = f.key;
					}
				} else { // [f: 0->a][i: 1->a] ---> [{0,1}->a]
					tree.replace(f, new Range<V>(f.key, index, value));
				}
			} else {
				if (isTailOf(c, index, value)) { // [f: {-1,0}->a][i: 1->a][c: 2->a] ---> [f: {-1,0,1,2}->a]
					tree.delete(c);
					f.key = c.key;
				} else { // [f: {-1,0}->a][i: 1->a] ---> [f: {0,1,2}->a]
					f.key = index;
				}
			}
		} else if (isTailOf(c, index, value)) {
			if (c.isPoint()) { // [i: 1->a][c: 2->a] ---> [{1,2}->a]
				tree.replace(c, new Range<V>(index, c.key, value));
			} else { // [i: 1->a][c: {2,3}->a] ---> [c: {1,2,3}->a]
				((Range<V>)c).min = index;
			}
		} else { // can't merge anything
			tree.insert(new Point<V>(index,value));
		}
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#put(int, Object)
	 */
	public V put(int index, V value) {
		Entry<V> c = tree.searchGTE(index);
		if (c==null || c.min() > index) { // we are adding a new index
			size++;
			merge(index, value, tree.searchLTE(index), c);
			return null;
		} else { // the index already exists
			if (equal(value, c.value)) {
				return value; // nothing to do
			} else if (c.isPoint()) {
				if (isHeadOf(tree.predecessor(c), index, value) || 
				    isTailOf(tree.successor(c), index, value)) {
					final V oldVal = remove(index);
					put(index, value);
					return oldVal;
				}
				return c.setValue(value);	
			} else { // split the range
				final V oldVal = split(index, c);
				tree.insert(new Point<V>(index,value));
				return oldVal;
			}
		}
		
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#get(int)
	 */
	public V get(int index) {
		final Entry<V> e = tree.searchGTE(index);
		return e==null || e.min() > index ? null : e.value;
	}

	/**
	 * Splits the z entry into the least number of entries
	 * that do not contain the given index.
	 * @requires z.min() <= index <= z.max()
	 * @requires z != NIL
	 * @ensures this.entries' = this.entries' - index->V
	 * @return z.value
	 */
	private V split(int index, Entry<V> z) {
		final V val = z.value;
		if (z.isPoint())
			tree.delete(z);
		else { // z contains a range of keys
			final Range<V> r = (Range<V>) z;
			final int min = r.min, max = r.key;
			if (min==index) {
				if (min+1<max)
					r.min++;
				else 
					tree.replace(r, new Point<V>(max, val));
			} else if (max==index) {
				if (max-1>min)
					r.key--;
				else
					tree.replace(r, new Point<V>(min, val));
			} else { // index is between min and max
				if (min==index-1) {
					tree.replace(r, new Point<V>(index-1, val));
					if (max==index+1) {
						tree.insert(new Point<V>(max, val));
					} else {
						r.min = index+1;
						tree.insert(r);
					}
				} else {
					r.key = index-1;
					if (max==index+1) {
						tree.insert(new Point<V>(max, val));
					} else {
						tree.insert(new Range<V>(index+1, max, val));
					}
				}
			}
		}
		return val;
	}
	
	/**
	 * Removes the entry with the given index, if it exists, and
	 * returns the value previously stored at the index.  If the
	 * sequence had no previous mapping for the index, null is returned.
	 * @ensures this.entries' = this.entries - index->E
	 * @return this.entries[index]
	 * @see kodkod.util.ints.SparseSequence#remove(int)
	 */
	public V remove(int index) {
		final Entry<V> z = tree.searchGTE(index);
		if (z==null || index < z.min()) return null;
		size--;
		return split(index,z);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#containsIndex(int)
	 */
	public boolean containsIndex(int index) {
		final Entry<V> e = tree.searchGTE(index);
		return e != null && e.min() <= index;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#first()
	 */
	public IndexedEntry<V> first() {
		final Entry<V> e = tree.min();
		return e==null ? null : view.setView(e.min(), e.value);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#last()
	 */
	public IndexedEntry<V> last() {
		final Entry<V> e = tree.max();
		return e==null ? null : view.setView(e.max(), e.value);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#ceil(int)
	 */
	public IndexedEntry<V> ceil(int index) {
		final Entry<V> e = tree.searchGTE(index);
		return e == null ? null : view.setView(StrictMath.max(index, e.min()), e.value);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.util.ints.SparseSequence#floor(int)
	 */
	public IndexedEntry<V> floor(int index) {
		Entry<V> e = tree.searchGTE(index);
		if (e==null || e.min() > index) {
			e = tree.searchLTE(index);
			return e == null ? null : view.setView(e.max(), e.value);
		} else
			return view.setView(index, e.value);
	}
	
	/**
	 * Returns a copy of this sparse sequence.  The copy is independent of this 
	 * sequence.
	 * @return a copy of this sparse sequence.
	 * @see kodkod.util.ints.SparseSequence#clone()
	 */
	public RangeSequence<V> clone() {
		// ok to use copy constructor to clone a final class
		return new RangeSequence<V>(this);
		
	}
	
	/**
	 * A mapping from range of integers in to a value
	 * @specfield min: int
	 * @specfield max: int
	 * @specfield value: V
	 * @invariant min <= max
	 * @invariant max = key
	 * @author Emina Torlak
	 */
	private static abstract class Entry<V> extends IntTree.Node<Entry<V>> implements Cloneable {
		V value;
		
		Entry(int max, V value) {
			super(max);
			this.value = value;
		}
		
		V setValue(V newValue) {
			final V oldValue = value;
			value = newValue;
			return oldValue;
		}
				
		/**
		 * Returns the minimum of this.
		 * @return this.min
		 */
		abstract int min();
		
		/**
		 * Returns the maximum of this.
		 * @return this.max
		 */
		final int max() { return key; }
				
		/**
		 * Return true if this.min=this.max
		 * @return this.min  = this.max
		 */
		abstract boolean isPoint();
		
		/**
		 * {@inheritDoc}
		 * @throws CloneNotSupportedException 
		 * @see java.lang.Object#clone()
		 */
		protected Entry<V> clone() throws CloneNotSupportedException {
			return (Entry<V>) super.clone();
		}
	}
	
	/**
	 * A point entry in a range sequence.
	 * @specfield min: int
	 * @specfield max: int
	 * @specfield value: V
	 * @specfield index: [min..max]
	 * @invariant min = max
	 */
	private static final class Point<V> extends Entry<V> {			
		/**
		 * Constructs an entry with the given index and value.
		 * @ensures this.index' = index && this.value' = value 
		 * @ensures this.min' = this.max' = index
		 */
		Point(int index, V value) {
			super(index, value);
		}
		
		@Override
		int min() { return key; }

		@Override
		boolean isPoint() { return true; }

		protected Point<V> clone() throws CloneNotSupportedException {
			return (Point<V>) super.clone();
		}
	}
	
	/**
	 * A range entry in a range sequence.
	 * @specfield min: int
	 * @specfield max: int
	 * @specfield value: V
	 * @invariant min < max
	 */
	private static final class Range<V> extends Entry<V> {
		int min;
		
		/**
		 * Constructs an entry with the given min/max and value.
		 * @ensures this.index' = min && this.value' = value 
		 * @ensures this.min' = min &&  this.max' = max
		 */
		Range(int min, int max, V value) {
			super(max, value);
			this.min = min;
		}
		
		@Override
		int min() { return min; }

		@Override
		boolean isPoint() { return false; }

		protected Range<V> clone() throws CloneNotSupportedException {
			return (Range<V>) super.clone();
		}
	}
	
	/**
	 * An iterator over the entries in this sequence.
	 */
	private abstract class EntryIterator implements Iterator<IndexedEntry<V>>, IndexedEntry<V> {
		final int endIndex;
		int endpoint, cursor, index;
		boolean canRemove;
		Entry<V> next;
		V value;
		
		/**
		 * @ensures this.endIndex' = endIndex && canRemove = false;
		 */
		EntryIterator(int endIndex) {
			this.endIndex = endIndex;
			this.canRemove = false;
		}
		
		public final int index() 	{	return index; }
		public final V value() 		{ 	return value; }
		
		public final boolean equals(Object o) {
			if (o==this) return true;
			if (!(o instanceof IndexedEntry)) return false;
			return AbstractSparseSequence.equal(this, (IndexedEntry<?>)o);
		}	
		
		public final int hashCode() {
			return AbstractSparseSequence.hashCode(this);
		}
		
		public final String toString() {
			return index + "=" + value;
		}
	}
	
	/**
	 * An iterator that returns the entries in this sequence 
	 * in the ascending order of indices.
	 * 
	 * @author Emina Torlak
	 */
	private final class AscendingIterator extends EntryIterator {
		
		/**
		 * Constructs an ascending iterator over the entries with
		 * indeces between from and to.
		 * @requires from <= to
		 */ 
		AscendingIterator(int from, int to) {
			super(to);
			next = tree.searchGTE(from);
			index = Integer.MIN_VALUE;
			if (next==null) {
				cursor = 0;
				endpoint = -1;
				value = null;
			} else {
				cursor = StrictMath.max(next.min(), from);
				endpoint = next.key;
				value = next.value;
				next = tree.successor(next);
			}
		}
				
		public boolean hasNext() {
			if (cursor > endpoint) {
				if (next==null) return false;
				this.cursor = next.min();
				this.endpoint = next.key; 
				this.value = next.value;
				next = tree.successor(next);
			}
			return index<Integer.MAX_VALUE && cursor <= endIndex;
		}

		public IndexedEntry<V> next() {
			if (!hasNext())
				throw new NoSuchElementException();
			index = cursor++;
			canRemove = true;
			return this;
		}

		public void remove() {
			if (!canRemove)
				throw new IllegalStateException();
			RangeSequence.this.remove(index);
			next = tree.searchGTE(cursor);
			canRemove = false;
		}
	}
	
	/**
	 * An iterator that returns the entries in this sequence 
	 * in the descending order of indices.
	 * 
	 * @author Emina Torlak
	 */
	private final class DescendingIterator extends EntryIterator {

		/**
		 * Constructs a descending iterator over the entries with
		 * indeces between from and to.
		 * @requires from >= to
		 */
		DescendingIterator(int from, int to) {
			super(to);
			next = tree.searchGTE(from);
			index = Integer.MAX_VALUE;
			if (next==null || next.min() > from) {
				next = tree.searchLTE(from);
				if (next==null) { 
					cursor = -1;
					endpoint = 0;
					value = null;
				} else {
					cursor = next.key;
					endpoint = next.min();
					value = next.value;
				}
			} else {
				cursor = StrictMath.min(next.key, from);
				endpoint = next.min();
				value = next.value;
				next = tree.predecessor(next);
			}
		}
	
		public boolean hasNext() { 
			if (cursor < endpoint) {
				if (next==null) return false;
				this.cursor = next.key;
				this.endpoint = next.min();
				this.value = next.value;
				next = tree.predecessor(next);
			}
			return index>Integer.MIN_VALUE && cursor >= endIndex;
		}
		public IndexedEntry<V> next() {
			if (!hasNext())
				throw new NoSuchElementException();
			index = cursor--;
			canRemove = true;
			return this;
		}
		public void remove() {
			if (!canRemove)
				throw new IllegalStateException();
			RangeSequence.this.remove((int) index);
			next = tree.searchLTE((int)cursor);
			canRemove = false;
		}
	}
}
