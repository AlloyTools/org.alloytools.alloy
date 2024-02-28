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

import kodkod.util.collections.Containers;
import kodkod.util.ints.IntRange.OnePointRange;
import kodkod.util.ints.IntRange.TwoPointRange;


/**
 * Contains various utility methods for working with
 * integers, {@link kodkod.util.ints.IntRange IntRanges},  
 * {@link kodkod.util.ints.IntSet IntSets}, and {@link kodkod.util.ints.SparseSequence SparseSequences}.
 * 
 * <p>The methods in this class all throw a NullPointerException if 
 * given a null reference unless otherwise specified.</p>
 * 
 * @author Emina Torlak
 */
public final class Ints {
	private static final int BITSET_CUTOFF = 1024;
	
	/** An immutable empty int set. The clone method returns the empty set itself. */
	public static final IntSet EMPTY_SET = 
		new AbstractIntSet() {
			public boolean contains(int i) { return false; }
			public int min() { throw new NoSuchElementException(); }
			public int max() { throw new NoSuchElementException(); }
			public IntIterator iterator(int from, int to) {	
				return new IntIterator() {
					public boolean hasNext() { return false; }
					public int next() { throw new NoSuchElementException(); }
					public void remove() { throw new UnsupportedOperationException(); }
				};
			}
			public int size() {	return 0; }
			public int floor(int i) { throw new NoSuchElementException(); }
			public int ceil(int i) { throw new NoSuchElementException(); }
			public IntSet clone() { return EMPTY_SET;}
	};
	
	/** An immutable empty sequence. The clone method returns the empty set itself. */
	public static final SparseSequence<?> EMPTY_SEQUENCE = 
		new AbstractSparseSequence<Object>() {
			public int size() { return 0; }
			public boolean containsIndex(int idx) { return false; }
			public boolean contains(Object o) { return false; }
			public IntSet indices() { return EMPTY_SET; }
			public Object get(int index) { return null;}
			public Iterator<IndexedEntry<Object>> iterator(int from, int to) { return Containers.emptyIterator(); }
			public SparseSequence<Object> clone() { return this; }
		};
	
	private Ints() {}

	/*-----------SETS AND RANGES-----------*/
	
	/**
	 * Returns an integer range from min, inclusive, to max, inclusive.
	 * @return { r: IntRange | r.min = min && r.max = max }
	 * @throws IllegalArgumentException  min > max
	 */
	public static IntRange range(int min, int max) {
		if (min < max) return new TwoPointRange(min,max);
		else if (min==max) return new OnePointRange(min);
		else throw new IllegalArgumentException("min > max");
	}
	
	/**
	 * Returns the smallest IntRange r that contains
	 * both r1 and r2.
	 * @return { r: IntRange | r.contains(r1) && r.contains(r2) && 
	 *           no r' : IntRange - r | r'.contains(r1) && r'.contains(r2) && r'.size() < r.size() }
	 * @throws NullPointerException  range = null
	 */
	public static IntRange merge(IntRange r1, IntRange r2) {
		if (r1.contains(r2)) return r1;
		else if (r2.contains(r1)) return r2;
		else return range(StrictMath.min(r1.min(),r2.min()), StrictMath.max(r1.max(), r2.max()));
	}
	
	/**
	 * Returns an unmodifiable view of the specified set. This method 
	 * allows modules to provide users with "read-only" access to internal int sets.
	 * Query operations on the returned set "read through" to the specified set, and 
	 * attempts to modify the returned set, whether direct or via its iterator, result 
	 * in an UnsupportedOperationException.  The clone() method of the returned set
	 * returns the result of calling s.clone().
	 * @return an unmodifiable view of s
	 * @throws NullPointerException  s = null
	 */
	public static IntSet unmodifiableIntSet(final IntSet s) {
		if (s==null) 
			throw new NullPointerException("s = null");
		else if (s instanceof UnmodifiableIntSet || s instanceof SingletonIntSet || s instanceof RangeIntSet)
			return s;
		else 
			return new UnmodifiableIntSet(s);
	}
	
	/**
	 * Returns an unmodifiable IntSet whose sole
	 * element is the given integer.  The clone method
	 * of the returned set returns the set itself.
	 * @return {s: IntSet | s.ints = i}
	 */
	public static IntSet singleton(final int i) {
		return new SingletonIntSet(i);
	}
	
	/**
	 * Returns an unmodifiable IntSet that contains
	 * all the elements in the given range.  The clone
	 * method of the returned set returns the set itself.
	 * @return {s: IntSet | s.ints = [range.min()..range.max()] }
	 */
	public static IntSet rangeSet(IntRange range) {
		if (range==null)
			throw new NullPointerException();
		return new RangeIntSet(range);
	}
	
	/**
	 * Returns an implementation of the int set interface
	 * that offers the best time/space trade-off for a 
	 * set that can store all elements in the half open
	 * range [0..max).  The returned instance may or may
	 * not admit elements out of the range [0..max).
	 * @return an int set that can store at least the 
	 * elements in [0..max).
	 */
	public static IntSet bestSet(int max) {
		return max > BITSET_CUTOFF ? new IntTreeSet() : new IntBitSet(max);
	}

	/**
	 * Returns an implementation of the int set interface
	 * that offers the best time/space trade-off for a 
	 * set that can store all elements in the closed range [min..max].  
	 * The returned instance may or may not admit elements 
	 * out of the specified range.
	 * @return an int set that can store at least the 
	 * elements in the given range.
	 * @throws IllegalArgumentException  min > max
	 */
	public static IntSet bestSet(int min, int max) {
		if (min > max) throw new IllegalArgumentException("min > max");
		return min < 0 ? new IntTreeSet() : bestSet(max+1);
	}
	
	/**
	 * Returns an IntSet that is backed by the given array of integers.
	 * The array must contain no duplicates, its elements must be sorted
	 * in the ascending order, and its contents
	 * must not be changed while it is in use by the returned set.
	 * @requires all i, j: [0..ints.length) | i < j => array[i] <= Sarray[j]
	 * @return an unmodifiable IntSet view of the given array
	 */
	public static IntSet asSet(int[] ints) {
		return ints.length==0 ? EMPTY_SET : new ArrayIntSet(ints);
	}
	
	/**
	 * Returns an unmodifiable IntArray backed by the given array of integers.
	 * @return an unmodifiable IntArray backed by the given array of integers.
	 */
	public static IntVector asIntVector(final int[] ints) {
		return new AbstractIntVector() {
			public int get(int index) { return ints[index]; }
			public int size() { return ints.length; }
			public int[] toArray(int[] array) { 
				if (array.length < ints.length) {
					array = new int[ints.length];
				}
				System.arraycopy(ints, 0, array, 0, ints.length); 
				return array;
			} 
		};
	}
	
	/**
	 * Returns an unmodifiable IntArray of length n which contains the given
	 * element at each position.
	 * @return an unmodifiable IntArray of length n which contains the given
	 * element at each position
	 */
	public static IntVector nCopies(final int n, final int elt) { 
		return new AbstractIntVector() {
			public int get(int index) { 
				if (index < 0 || index >= n) throw new IndexOutOfBoundsException();
				return elt;
			}
			public int size() { return n; }
			public int[] toArray(int[] array) { 
				if (array.length < n) {
					array = new int[n];
				}
				for(int i = 0; i < n; i++) { array[i] = elt; }
				return array;
			} 
		};
	}
	
	/*-----------SEQUENCES-----------*/
	
	/**
	 * Returns {@linkplain #EMPTY_SEQUENCE} cast to a sequence of type SparseSequence<V>.
	 * @return {@linkplain #EMPTY_SEQUENCE}
	 */
	@SuppressWarnings("unchecked")
	public static <V> SparseSequence<V> emptySequence() { 
		return (SparseSequence<V>) EMPTY_SEQUENCE;
	}
	
	/**
	 * Returns an unmodifiable view of the specified sparse sequence. This method 
	 * allows modules to provide users with "read-only" access to internal sparse sequences.
	 * Query operations on the returned sequence "read through" to the specified sequence, and 
	 * attempts to modify the returned sequence, whether direct or via its iterator, result 
	 * in an UnsupportedOperationException.  The clone() method of the returned sequence
	 * returns the result of calling s.clone().
	 * @return an unmodifiable view of s
	 * @throws NullPointerException  s = null
	 */
	public static <V> SparseSequence<V> unmodifiableSequence(SparseSequence<V> s) {
		if (s==null) 
			throw new NullPointerException();
		if (s instanceof UnmodifiableSparseSequence)
			return s;
		else return new UnmodifiableSparseSequence<V>(s);
	}
	
	/*-----------INTEGER MANIPULATION-----------*/
	
	/**
	 * Returns an integer whose value is the 16 low order bits of the given key.
	 * @return key & 0x0000ffff
	 */
	private static int low16(int key) {
		return key & 0x0000ffff;
	}
	
	/**
	 * Returns an integer whose value is the 16 high order bits of the given key.
	 * @return (key >>> 16) & 0x0000ffff
	 */
	private static int high16(int key) {
		return low16(key>>>16);
	}
	
	/**
	 * Performs the bit avalanching step of Paul Hsieh's
	 * hashing function (http://www.azillionmonkeys.com/qed/hash.html)
	 * @return the bit avalanched version of the given hash value
	 */ 
	public static int superFastHashAvalanche(int hash) {
		hash ^= hash << 3;
		hash += hash >> 5;
		hash ^= hash << 4;
		hash += hash >> 17;
		hash ^= hash << 25;
		hash += hash >> 6;
		return hash;
	}
	
	/**
	 * Performs the hashing step of Paul Hsieh's hashing function, 
	 * described at http://www.azillionmonkeys.com/qed/hash.html.
	 * The method returns a 32 bit hash of the given integer, starting
	 * with the given initial hash.  <b>This method does not perform 
	 * bit avalanching.</b>  To get the full hash, call {@linkplain #superFastHashAvalanche(int)}
	 * on the value returned by this method.
	 * @return a 32 bit hash of the given integer, based on the given hash
	 */
	public static int superFastHashIncremental(int key, int hash) {

		hash += low16(key);
		final int tmp = (high16(key) << 11) ^ hash;
		hash = (hash << 16) ^ tmp;
		hash += hash >> 11;
		
		// no end cases since the key has exactly 4 bytes
		return hash;
	}
	
	/**
	 * An implementation of Paul Hsieh's hashing function, 
	 * described at http://www.azillionmonkeys.com/qed/hash.html.
	 * The method returns a 32 bit hash of the given integer.
	 * This function is very fast and collision resistent; e.g. 
	 * it hashes the four million integers in the range 
	 * [-2000000,...-1, 1,..., 2000000] to distinct values.
	 * The initial hash is taken to be 11.
	 * @return a 32 bit hash of the given integer
	 */
	public static int superFastHash(int key) {
		return superFastHashAvalanche(superFastHashIncremental(key, 11));
	}
	
	/**
	 * An implementation of Paul Hsieh's hashing function, 
	 * described at http://www.azillionmonkeys.com/qed/hash.html.
	 * The method returns a 32 bit hash of the given integers,
	 * or 0 if the array is empty. The initial hash is taken to be
	 * the number of keys.
	 * @return a 32 bit hash of the given integers
	 */
	public static int superFastHash(int... key) {
		if (key.length==0) return 0;
		int hash = key.length;

		for(int word : key) {
			hash = superFastHashIncremental(word, hash);
		}
		// no end cases since key parts are ints
		return superFastHashAvalanche(hash);
	}
	
	/**
	 * An implementation of Paul Hsieh's hashing function, 
	 * described at http://www.azillionmonkeys.com/qed/hash.html.
	 * The method returns a 32 bit hash of the given objects' hash codes,
	 * or zero if the array is empty.  Any null references in the array
	 * are taken to have 0 as their hash code value.
	 * @return a 32 bit hash of the given objects' hashCodes
	 */
	public static int superFastHash(Object... key) {
		if (key.length==0) return 0;
		int hash = key.length; 

		for(Object o : key) {
			hash = superFastHashIncremental(o == null ? 0 : o.hashCode(), hash);
		}
		//	no end cases since the hashcodes of key parts are ints
		return superFastHashAvalanche(hash);
	}
	
	/**
	 * An implementation of an IntSet wrapper for an IntRange.
	 */
	private static final class RangeIntSet extends AbstractIntSet {
		private final IntRange range;
		/**
		 * Constructs an unmodifiable IntSet wrapper for a range.
		 */
		RangeIntSet(IntRange range) {
			this.range = range;
		}
		public boolean contains(int i) { return range.contains(i); }
		public int min() { return range.min(); }
		public int max() { return range.max(); }
		public IntIterator iterator(final int from, final int to) {
			return new IntIterator() {
				final boolean ascending = (from <= to);
				long cursor = ascending ? StrictMath.max(range.min(), from) : StrictMath.min(range.max(), from);
				final int end = ascending ? StrictMath.min(range.max(), to) : StrictMath.max(range.min(), to);
				public boolean hasNext() {
					return ascending && cursor<=end || !ascending && cursor >= end;
				}
				public int next() {
					if (!hasNext()) throw new NoSuchElementException();
					return ascending ? (int)cursor++ : (int)cursor--;
				}
				public void remove() { throw new UnsupportedOperationException(); }
				
			};
		}
		public int size() {	return range.size(); }
		public int floor(int i) {
			if (i<range.min())
				throw new NoSuchElementException();
			return StrictMath.min(i, range.max());
		}
		public int ceil(int i) {
			if (i>range.max())
				throw new NoSuchElementException();
			return StrictMath.max(i, range.min());
		}
		public IntSet clone() { return this; }
	}
	
	/**
	 * An implementation of an IntSet wrapper for a single integer.
	 */
	private static final class SingletonIntSet extends AbstractIntSet {
		private final int i;
		/**
		 * Constructs an unmodifiable intset wrapper for the given integer.
		 */
		SingletonIntSet(int i) {
			this.i = i;
		}
		public boolean contains(int j) { return i==j; }
		public int min() { return i; }
		public int max() { return i; }
		public IntIterator iterator(final int from, final int to) {	
			return new IntIterator() {
				boolean cursor = (from<=i && i<=to) || (to<=i && i<=from);
				public boolean hasNext() { return cursor; }
				public int next() { 
					if (!hasNext()) throw new NoSuchElementException(); 
					cursor = false;
					return i;
				}
				public void remove() { throw new UnsupportedOperationException(); }
			};
		}
		public int size() {	return 1; }
		public boolean equals(Object o) {
			if (this==o) return true;
			else if (o instanceof IntSet) {
				final IntSet s = (IntSet) o;
				return s.size()==1 && s.min()==i;
			} else
				return super.equals(o);
		}
		public int hashCode() { return i; }
		public int floor(int j) {
			if (i<=j) return i;
			else throw new NoSuchElementException();
		}
		public int ceil(int j) {
			if (i>=j) return i;
			else throw new NoSuchElementException();
		}
		public IntSet clone() { return this; }
	}
	
	/**
	 * An implementation of an unmodifiable IntSet view.
	 * @author Emina Torlak
	 */
	private static final class UnmodifiableIntSet extends AbstractIntSet {
		private final IntSet s;
		
		/**
		 * Constructs an unmodifiable wrapper for the given intset.
		 * @requires set != null
		 */
		UnmodifiableIntSet(IntSet set) {
			this.s = set;
		}
		public int size() { return s.size(); }
		public boolean contains(int i) { return s.contains(i); }
		public int min() { return s.min();	}
		public int max() { return s.max();	}
		public IntIterator iterator(final int from, final int to) { 	
			return new IntIterator() {
				IntIterator iter = s.iterator(from,to);
				public boolean hasNext() { return iter.hasNext(); }
				public int next() { return iter.next(); }
				public void remove() {
					throw new UnsupportedOperationException();
				}	
			};
		}
		public int floor(int i) { return s.floor(i); }
		public int ceil(int i) { return s.ceil(i); }
		public IntSet clone() throws CloneNotSupportedException { return s.clone(); }
	}
	
	/**
	 * An implementation of an unmodifiable SparseSequence view.
	 * @author Emina Torlak
	 */
	private static final class UnmodifiableSparseSequence<V> extends AbstractSparseSequence<V> {
		private final SparseSequence<V> s;
		
		UnmodifiableSparseSequence(SparseSequence<V> s) {
			this.s = s;
		}
		
		public Iterator<IndexedEntry<V>> iterator(final int from, final int to) {
			return new Iterator<IndexedEntry<V>>() {
				Iterator<IndexedEntry<V>> iter = s.iterator(from, to);
				public boolean hasNext() {
					return iter.hasNext();
				}

				public IndexedEntry<V> next() {
					return iter.next();
				}

				public void remove() {
					throw new UnsupportedOperationException();
				}
				
			};
		}

		public int size() {					return s.size(); }
		public void clear() {				throw new UnsupportedOperationException(); }
		public V put(int index, V value) {	throw new UnsupportedOperationException(); }
		public V get(int index) { 			return s.get(index); }
		public V remove(int index) {		throw new UnsupportedOperationException(); }
		public IndexedEntry<V> first() {	return s.first(); }
		public IndexedEntry<V> last() {		return s.last(); }
		
		public IndexedEntry<V> ceil(int index) {	return s.ceil(index); }
		public IndexedEntry<V> floor(int index) {	return s.floor(index); }
		public boolean containsIndex(int index) {	return s.containsIndex(index); }
		public boolean contains(Object value) {		return s.contains(value); }
		
		public SparseSequence<V> clone() throws CloneNotSupportedException {
			return s.clone();
		}
		
	}
}
