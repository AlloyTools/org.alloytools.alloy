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
package kodkod.instance;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;

import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;


/**
 * Represents a set of {@link kodkod.instance.Tuple tuples}
 * of a given arity, constructed over a given {@link kodkod.instance.Universe universe}.
 * All polymorphic methods throw a ClassCastException when passed
 * an element that is not a Tuple.  All methods throw a NullPointerException
 * when passed null.  The iterator of a TupleSet returns tuples in the order of their
 * {@link kodkod.instance.Tuple#index() indeces}.  
 * 
 * @specfield tuples: set Tuple
 * @specfield universe: Universe
 * @specfield arity: int
 * @invariant tuples.arity = arity && tuples.universe = universe
 * 
 * @author Emina Torlak
 */
public final class TupleSet extends AbstractSet<Tuple> implements Cloneable {
	private final Universe universe;
	private final int arity;
	private final IntSet tuples;
	private IntSet indexView = null;
		
	/**
	 * Constructs an empty tuple set for storing tuples
	 * of the specified arity, over the given universe.
	 * 
	 * @ensures this.universe' = universe && this.arity' = arity && no this.tuples'
	 * @throws NullPointerException  universe = null
	 * @throws IllegalArgumentException  arity < 1
	 */
	TupleSet(Universe universe, int arity) {
		if (arity < 1) throw new IllegalArgumentException("arity < 1");
		universe.factory().checkCapacity(arity);
		this.universe = universe;
		this.arity = arity;
		tuples = Ints.bestSet(capacity());
	}
	
	/**
	 * Constructs a tuple set of the given arity, over the specified universe,
	 * which initially contains all tuples whose indeces are between fromIndex
	 * and toIndex, inclusive.
	 * 
	 * @ensures this.universe' = universe && this.arity' = arity && 
	 *          this.tuples' = {t: Tuple | t.universe=universe && t.arity=arity && 
	 *                                     fromIndex()<=t.index()<=toIndex() }
	 * @throws NullPointerException  universe = null 
	 * @throws IllegalArgumentException  arity < 1 || 
	 * @throws IndexOutOfBoundsException  fromIndex !in [0..toIndex] ||
	 *                                     toIndex !in [0..universe.size()^arity - 1]
	 */
	TupleSet(Universe universe, int arity, int fromIndex, int toIndex) {
		this(universe,arity);
		checkRange(toIndex, 0, capacity() - 1);
		checkRange(fromIndex, 0, toIndex);
		for(int i = fromIndex; i <= toIndex; i++) {
			tuples.add(i);
		}
	}
	
	/**
	 * Returns a set of the given arity that contains all tuples whose indeces
	 * are contained in the given int set.  Throws an IllegalArgumentException
	 * if the set contains an index that is either negative or greater than
	 * this.universe.size()^arity - 1.  An attempt to iterate over a tuple set backed by an invalid index
	 * set will result in a runtime exception.  
	 * @return {s: TupleSet | s.universe = this.universe && s.arity = arity &&
	 *                        s.tuples = {t: Tuple | t.index() in tupleIndeces} }
	 * @throws NullPointerException  tupleIndeces = null
	 * @throws IllegalArgumentException  arity < 1
	 * @throws IllegalArgumentException  tupleIndeces.min() < 0 || tupleIndeces.max() >= this.universe.size()^arity 
	 */
	TupleSet(Universe universe, int arity, IntSet tupleIndeces) {
		if (arity < 1) throw new IllegalArgumentException("arity < 1");
		universe.factory().checkCapacity(arity);
		this.universe = universe;
		this.arity = arity;
		if (!tupleIndeces.isEmpty()) {
			if (tupleIndeces.min()<0 || tupleIndeces.max() >= capacity())
				throw new IllegalArgumentException(tupleIndeces.min() + "<0 || " + tupleIndeces.max()+">="+universe.size()+"^"+arity);
		}
		tuples = tupleIndeces;
	}
	
	/**
	 * Copy constructor.
	 * @ensures constructs a deep copy of the given tupleset
	 */
	private TupleSet(TupleSet original) {
		this.universe = original.universe;
		this.arity = original.arity;
		try {
			this.tuples = original.tuples.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError(); // unreachable code
		}
		this.indexView = null;
	}
	
	/**
	 * Throws an IndexOutOfBoundsException if index is not in [min..max]
	 */
	private final void checkRange(int index, int min, int max) {
		if (index < min || index > max)
			throw new IndexOutOfBoundsException(index + " !in " + "[" + min + ".." + max + "]");
	}
	
	/**
	 * Returns the capacity of this set -- the maximum number of tuples
	 * that it can hold, given its universe and arity.  
	 * @return this.universe.size() ^ this.arity
	 */
	public final int capacity() {
		return (int) StrictMath.pow(universe.size(),arity);
	}

	/**
	 * Returns this.universe.
	 * @return this.universe
	 */
	public Universe universe() { return universe; }
	
	/**
	 * Returns this.arity
	 * @return this.arity
	 */
	public int arity() { return arity; }
	
	
	
	/**
	 * Returns an unmodifiable int set view of the tuples stored in this set.
	 * Specifically, the returned int set contains an integer i
	 * iff this set contains a tuple with the index i.  The 
	 * view is backed by this set, so changes to this set are
	 * reflected in the index set. 
	 * @return { s: IntSet | s.ints = {i: int | some t: this.tuples | t.index = i}
	 */
	public IntSet indexView() {
		if (indexView==null) {
			indexView = Ints.unmodifiableIntSet(tuples);
		}
		return indexView;
	}
	
	/**
	 * Returns an unmodifiable view of the this tupleset.  This method allows modules to 
	 * provide "read-only" access to internal tuple sets. Query operations on the returned set 
	 * "read through" to the specified set, and attempts to modify the returned set, whether direct 
	 * or via its iterator, result in an UnsupportedOperationException.
	 * @return an unmodifiable view of the this tupleset
	 */
	public TupleSet unmodifiableView() {
		return new TupleSet(universe,arity,indexView());
	}
	
	/**
	 * Returns a tuple set that is the cross product of this and the 
	 * specified set.
	 * @return {t: TupleSet | t.arity = this.arity + s.arity &&
	 *                        t.universe = this.universe &&
	 *                        t.tuples = this.tuples->s.tuples }
	 * @throws NullPointerException  s = null
	 * @throws IllegalArgumentException  s.universe != this.universe                              
	 */
	public TupleSet product(TupleSet s) {
		if (!s.universe().equals(universe))
			throw new IllegalArgumentException("s.universe != this.universe");
		final TupleSet ret = new TupleSet(universe, arity+s.arity());
		if (!s.isEmpty()) {
			final int mCapacity = (int) StrictMath.pow(universe.size(), s.arity);
			for(IntIterator indeces0 = tuples.iterator(); indeces0.hasNext(); ) {
				int i0 = mCapacity * indeces0.next();
				for(IntIterator indeces1 = s.tuples.iterator(); indeces1.hasNext(); ) {
					ret.tuples.add(i0 + indeces1.next());
				}
			}
		}
		return ret;
	}
	
	/**
	 * Projects this TupleSet onto the given dimension.
	 * @return {s: TupleSet | s.arity = 1 && s.universe = this.universe && 
	 *                        s.tuples = { t: Tuple | some q: this.tuples | q.atoms[dimension] = t.atoms[int] } }
	 * @throws IllegalArgumentException  dimension < 0 || dimension >= this.arity
	 */
	public TupleSet project(int dimension) {
		if (dimension < 0 || dimension >= arity) {
			throw new IllegalArgumentException("dimension < 0 || dimension >= this.arity");
		}
		final IntSet projection = Ints.bestSet(universe.size());
		final TupleFactory factory = universe.factory();
		for(IntIterator indexIter = tuples.iterator(); indexIter.hasNext();) {
			projection.add(factory.project(indexIter.next(), arity, dimension));
		}
		return new TupleSet(universe,1,projection);
	}
	
	/**
	 * Returns a deep copy of this tuple set. 
	 * @return {s: TupleSet - this | s.universe = this.universe && s.tuples = this.tuples }
	 */
	public TupleSet clone() {
		// ok to use a copy constructor to clone a final class
		return new TupleSet(this);
	}
	
	/**
	 * Returns an iterator over the tuples in this tupleset.
	 * @return an iterator over the tuples in this tupleset.
	 */
	@Override
	public Iterator<Tuple> iterator() {
		return new Iterator<Tuple>() {
			IntIterator indexIter = tuples.iterator();
			public boolean hasNext() {
				return indexIter.hasNext();
			}

			public Tuple next() {
				return universe.factory().tuple(arity, indexIter.next());
			}

			public void remove() {
				indexIter.remove();
			}
		};
	}
	
	/**
	 * Returns the index of the given tuple, if the tuple has the same
	 * arity and universe as this.  Otherwise throws an IllegalArgumentException.
	 * @return t.index
	 * @throws IllegalArgumentException  t.arity != this.arity || t.universe != this.universe
	 */
	private final int extractIndex(Tuple t) {
		if (t.arity() != arity || !t.universe().equals(universe)) {
			throw new IllegalArgumentException("t.arity != this.arity || t.universe != this.universe");
		}
		return t.index();
	}
	
	/**
	 * Returns true if this contains the given object.
	 * @return o in this.tuples
	 * @throws IllegalArgumentException o.arity != this.arity || o.universe != this.universe
	 */
	@Override
	public boolean contains(Object o) {
		return tuples.contains(extractIndex((Tuple)o));
	}
	
	/**
	 * Returns the size of this tupleset.
	 * @return #this.tuples
	 */
	@Override
	public int size() { return tuples.size(); }
	
	/**
	 * Removes all tuples from this tupleset.
	 * @ensures no this.tuples' 
	 */
	@Override
	public void clear() { 
		tuples.clear(); 
	}

	/**
	 * Adds the specified tuple to this tupleset.  Returns
	 * true if this set was changed as the result of the
	 * operation.
	 * @ensures this.tuples' = this.tuples + t
	 * @return o !in this.tuples
	 * @throws IllegalArgumentException  t.universe != this.universe || t.arity != this.arity
	 */
	@Override
	public boolean add(Tuple t) {
		return tuples.add(extractIndex(t));
	}

	/**
	 * Removes the given object from this tupleset, if present, and
	 * returns true.  Otherwise does nothing and returns false.
	 * @ensures this.tuples' = this.tuples - o
	 * @return o in this.tuples
	 * @throws IllegalArgumentException  o.universe != this.universe || o.arity != this.arity
	 */
	@Override
	public boolean remove(Object o) {
		return tuples.remove(extractIndex((Tuple)o));
	}
	
	/**
	 * If c is not a TupleSet or it is a tupleset with a universe different than
	 * this.universe, returns null.  Otherwise, returns the tuples associated 
	 * with the modifiable view of c. 
	 * @requires c in TupleSet => c.arity = this.arity
	 * @return c in TupleSet && c.universe = this.universe && c.arity = this.arity => c.tuples, null
	 * @throws NullPointerException  s = null
	 * @throws IllegalArgumentException  this.arity!=s.arity
	 */
	private IntSet extractTuples(Collection<?> c) {
		if (c instanceof TupleSet) {
			final TupleSet s = (TupleSet) c;
			if (arity!=s.arity())
				throw new IllegalArgumentException("this.arity!=c.arity");
			return universe.equals(s.universe()) ? s.tuples : null;
		}
		return null;
	}
	
	/**
	 * Returns true if this contains all tuples from c.  Otherwise returns false.
	 * @return c.elements in this.tuples
	 * @throws IllegalArgumentException  some t: c.elements | t.universe != this.universe || t.arity != this.arity
	 */
	@Override
	public boolean containsAll(Collection<?> c) { 
		final IntSet cTuples = extractTuples(c);
		return cTuples==null ? super.containsAll(c) : tuples.containsAll(cTuples);
	}
	
	/**
	 * Adds all tuples from c to this, if not present, and returns
	 * true.  Otherwise does nothing and returns false.
	 * @ensures this.tuples' = this.tuples + c.elements
	 * @return c.elements !in this.tuples
	 * @throws IllegalArgumentException  some t: c.elements | t.universe != this.universe || t.arity != this.arity
	 */
	@Override
	public boolean addAll(Collection<? extends Tuple> c) {
		final IntSet cTuples = extractTuples(c);
		return cTuples==null ? super.addAll(c) : tuples.addAll(cTuples);
	}
	
	/**
	 * Removes all tuples in c from this, if present, and returns
	 * true.  Otherwise does nothing and returns false.
	 * @ensures this.tuples' = this.tuples - c.elements
	 * @return some c.elements & this.tuples
	 * @throws IllegalArgumentException  some t: c.elements | t.universe != this.universe || t.arity != this.arity
	 */
	@Override
	public boolean removeAll(Collection<?> c) {
		final IntSet cTuples = extractTuples(c);
		return cTuples==null ? super.removeAll(c) : tuples.removeAll(cTuples);
	}
	
	/**
	 * Removes all tuples from this that are not in c, if any, and
	 * returns true. Otherwise does nothing and returns false.
	 * @ensures this.tuples' = this.tuples & c.elements
	 * @return this.tuples !in c.elements
	 * @throws IllegalArgumentException  some t: c.elements | t.universe != this.universe || t.arity != this.arity
	 */
	@Override
	public boolean retainAll(Collection<?> c) {
		final IntSet cTuples = extractTuples(c);
		return cTuples==null ? super.retainAll(c) : tuples.retainAll(cTuples);
	}
	
	
	/**
	 * Returns true if o contains the same tuples as this.
	 * @return this.tuples = o.elements
	 */
	@Override
	public boolean equals(Object o) {
		if (this==o) return true;
		if (o instanceof TupleSet) {
			final TupleSet s = (TupleSet) o;
			return arity==s.arity && universe.equals(s.universe) && 
			       tuples.equals(s.tuples);
		}
		return super.equals(o);
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public int hashCode() { 
		return tuples.hashCode();
	}
}
