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
package kodkod.util.collections;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;


/**
 * A map with a fixed set of keys that acts as an indexer, assigning a
 * unique integer in the range [0..#keys) to each key.  This class implements the 
 * <tt>Map</tt> interface with an array, using
 * reference-equality in place of object-equality when comparing keys (and
 * values).  In other words, in a <tt>FixedMap</tt>, two keys
 * <tt>k1</tt> and <tt>k2</tt> are considered equal if and only if
 * <tt>(k1==k2)</tt>.  (In normal <tt>Map</tt> implementations (like
 * <tt>HashMap</tt>) two keys <tt>k1</tt> and <tt>k2</tt> are considered equal
 * if and only if <tt>(k1==null ? k2==null : k1.equals(k2))</tt>.)</p>
 * 
 * <p><b>This class is <i>not</i> a general-purpose <tt>Map</tt>
 * implementation!  While this class implements the <tt>Map</tt> interface, it
 * intentionally violates <tt>Map's</tt> general contract, which mandates the
 * use of the <tt>equals</tt> method when comparing objects.  </b></p>
 * 
 * <p>This class provides {@link #put(Object, Object)} operation for the keys
 * within its fixed key set and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  The {@link #remove(Object)} 
 * operation is not supported.  This class guarantees
 * that the order of the map will remain constant over time.</p>
 *
 * <p>This class provides log-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the system
 * identity hash function ({@link System#identityHashCode(Object)})
 * disperses elements properly among the buckets.</p>
 * 
 * <p>This implementation is not synchronized, and its iterators are not fail-fast.</p>
 * 
 * @specfield keys: set K
 * @specfield map: keys -> one V
 * @specfield indices: keys lone->one [0..#keys) 
 * @author Emina Torlak
 */
public final class FixedMap<K, V> extends AbstractMap<K, V> implements Indexer<K> {

	private final Object[] keys;
	private final Object[] values;

	/**
	 * Constructs a new fixed map from the given map.
	 * @ensures this.keys' = keys && this.map = map.map
	 */
	public FixedMap(Map<K, V> map) {
		this(map.keySet());
		for(int i = 0, size = map.size(); i < size; i++) {
			values[i] = map.get(keys[i]);
		}
	}

	/**
	 * Constructs a new fixed map for the given set of keys.
	 * @ensures this.keys' = keys && no this.map'
	 */
	public FixedMap(Set<K> keys) {
		final int size = keys.size();
		this.keys = Containers.identitySort(keys.toArray(new Object[size]));
		values = new Object[size];
	}

	/**
	 * Constructs a new fixed map, backed by the given array of keys.  The provided
	 * array must not contain duplicates, its entries must be sorted
	 * in the increasing order of identity hashcodes, and it must not
	 * be modified while in use by this map.  The map will not behave correctly if
	 * these requirements are violated.
	 * @requires no disj i, j: [0..keys.length) | keys[i] == keys[j]
	 * @requires all i, j: [0..keys.length) | i < j => System.identityHashCode(keys[i]) <= System.identityHashCode(keys[j])
	 * @ensures this.keys' = keys && no this.map'
	 */
	public FixedMap(K[] keys) {
		this.keys = keys;
		this.values = new Object[keys.length];
	}
	
	/**
	 * Returns the index of the given key, if it is in this.keys.
	 * Otherwise returns a negative number.
	 * @return key in this.keys => this.indices[key], {i: int | i < 0 }
	 */
	public final int indexOf(K key) {
		return Containers.identityBinarySearch(keys, key);
	}

	/**
	 * Returns the key at the given index.
	 * @return this.indices.index
	 * @throws IndexOutOfBoundsException  index !in this.indices[this.keys]
	 */
	@SuppressWarnings("unchecked")
	public final K keyAt(int index) {
		try {
			return (K)keys[index];
		} catch (ArrayIndexOutOfBoundsException e) {
			throw new IndexOutOfBoundsException();
		}
	}
	
	/**
     * Tests whether the specified object reference is a key in this fixed map.
     *
     * @return key in this.keys
     */
	@SuppressWarnings("unchecked")
	public final boolean containsKey(Object key) {
		return indexOf((K)key) >= 0;
	}

	 /**
     * Tests whether the specified object reference is a value in this fixed map.
     *
     * @return value in this.map[this.keys]
     */
	public final boolean containsValue(Object value) {
		for(Object o : values) {
			if (o==value) return true;
		}
		return false;
	}

	/**
     * Returns a set view of the mappings contained in this map.  Each element
     * in the returned set is a reference-equality-based <tt>Map.Entry</tt>.
     * The set is backed by the map, so changes to the map are reflected in
     * the set, and vice-versa.  If the map is modified while an iteration
     * over the set is in progress, the results of the iteration are
     * undefined.  The set does support neither removal nor addition.
     *
     * <p>Like the backing map, the <tt>Map.Entry</tt> objects in the set
     * returned by this method define key and value equality as
     * reference-equality rather than object-equality.  This affects the
     * behavior of the <tt>equals</tt> and <tt>hashCode</tt> methods of these
     * <tt>Map.Entry</tt> objects.  A reference-equality based <tt>Map.Entry
     * e</tt> is equal to an object <tt>o</tt> if and only if <tt>o</tt> is a
     * <tt>Map.Entry</tt> and <tt>e.getKey()==o.getKey() &&
     * e.getValue()==o.getValue()</tt>.  To accommodate these equals
     * semantics, the <tt>hashCode</tt> method returns
     * <tt>System.identityHashCode(e.getKey()) ^
     * System.identityHashCode(e.getValue())</tt>.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * <tt>Map.Entry</tt> instances in the set returned by this method,
     * it is possible that the symmetry and transitivity requirements of
     * the {@link Object#equals(Object)} contract may be violated if any of
     * the entries in the set is compared to a normal map entry, or if
     * the set returned by this method is compared to a set of normal map
     * entries (such as would be returned by a call to this method on a normal
     * map).  However, the <tt>Object.equals</tt> contract is guaranteed to
     * hold among identity-based map entries, and among sets of such entries.
     * </b>
     *
     * @return a set view of the identity-mappings contained in this map.
     */
	public final Set<Map.Entry<K, V>> entrySet() {
		return new AbstractSet<Map.Entry<K, V>>() {

			@SuppressWarnings("unchecked")
			public boolean contains(Object o) {
				final Map.Entry<K, V> e = (Map.Entry<K, V>) o;
				final int index = FixedMap.this.indexOf(e.getKey());
				return index < 0 ? false : values[index]==e.getValue();
			}

			public Iterator<java.util.Map.Entry<K, V>> iterator() {	return new EntryIterator(); }

			public int size() { return keys.length; }

			public Object[] toArray() {
				int size = size();
				Object[] result = new Object[size];
				for (int i = 0; i < size; i++)
					result[i] = new Entry(i);
				return result;
			}

			@SuppressWarnings("unchecked")
			public <T> T[] toArray(T[] a) {
				int size = size();
				if (a.length < size)
					a = (T[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
				for (int i = 0; i < size; i++)
					a[i] = (T) new Entry(i);
				if (a.length > size)
					a[size] = null;
				return a;
			}
		};
	}

	/**
     * Returns the value to which the specified key is mapped in this fixed map, 
     * or <tt>null</tt> if the map contains no mapping for
     * this key.  A return value of <tt>null</tt> does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it is also
     * possible that the map explicitly maps the key to <tt>null</tt>. The
     * <tt>containsKey</tt> method may be used to distinguish these two
     * cases.
     *
     * @return  this.map[key]
     */
	@SuppressWarnings("unchecked")
	public final V get(Object key) {
		final int index = indexOf((K)key);
		return index < 0 ? null : (V)values[index];
	}

	/**
	 * Returns the value to which the key at the specified index is mapped in this fixed map.
	 * @requires index in this.indices[this.keys]
	 * @return this.map[this.indices.index]
	 * @throws IndexOutOfBoundsException  index !in this.indices[this.keys]
	 */
	@SuppressWarnings("unchecked")
	public final V get(int index) {
		try {
			return (V) values[index];
		} catch (ArrayIndexOutOfBoundsException e) {
			throw new IndexOutOfBoundsException();
		}
	}
	
	/**
	 * @see java.util.Map#isEmpty()
	 */
	public final boolean isEmpty() {
		return keys.length==0;
	}

	 /**
     * Associates the specified value with the specified key in this fixed
     *  map.  If the map previously contained a mapping for this key, the
     * old value is replaced.  This method assumes that the given key is 
     * in the fixed keyset of this map.
     *
     * @requires key in this.keys
     * @return this.map[key]
     * @ensures this.map' = this.map ++ key->value
     * @throws IllegalArgumentException  key !in this.keys
     */

	@SuppressWarnings("unchecked")
	public final V put(K key, V value) {
		final int index = indexOf((K)key);
		if (index < 0) throw new IllegalArgumentException();
		final V oldValue = (V) values[index];
		values[index] = value;
		return oldValue;
	}

	/**
	 * Throws an {@link UnsupportedOperationException} exception.
	 * @see java.util.Map#remove(java.lang.Object)
	 */
	public final V remove(Object key) {
		throw new UnsupportedOperationException();
	}

	/**
	 * @see java.util.Map#size()
	 */
	public final int size() {
		return keys.length;
	}

	/**
	 * Returns the hash code value for this map.  The hash code of a map
	 * is defined to be the sum of the hashcode of each entry in the map's
	 * entrySet view.  This ensures that <tt>t1.equals(t2)</tt> implies
	 * that <tt>t1.hashCode()==t2.hashCode()</tt> for any two
	 * <tt>FixedMap</tt> instances <tt>t1</tt> and <tt>t2</tt>, as
	 * required by the general contract of {@link Object#hashCode()}.
	 *
	 * <p><b>Owing to the reference-equality-based semantics of the
	 * <tt>Map.Entry</tt> instances in the set returned by this map's
	 * <tt>entrySet</tt> method, it is possible that the contractual
	 * requirement of <tt>Object.hashCode</tt> mentioned in the previous
	 * paragraph will be violated if one of the two objects being compared is
	 * an <tt>FixedMap</tt> instance and the other is a normal map.</b>
	 *
	 * @return the hash code value for this map.
	 * @see Object#hashCode()
	 * @see Object#equals(Object)
	 * @see #equals(Object)
	 */
	public int hashCode() {
		int result = 0;
		for(int i = 0 ; i < keys.length; i++) 
			result += System.identityHashCode(keys[i]) ^ System.identityHashCode(values[i]);
		return result;
	}

	/**
     * Compares the specified object with this map for equality.  Returns
     * <tt>true</tt> if the given object is also a map and the two maps
     * represent identical object-reference mappings.  More formally, this
     * map is equal to another map <tt>m</tt> if and only if
     * map <tt>this.entrySet().equals(m.entrySet())</tt>.
     *
     * <p><b>Owing to the reference-equality-based semantics of this map it is
     * possible that the symmetry and transitivity requirements of the
     * <tt>Object.equals</tt> contract may be violated if this map is compared
     * to a normal map.  However, the <tt>Object.equals</tt> contract is
     * guaranteed to hold among <tt>FixedMap</tt> instances.</b>
     *
     * @param  o object to be compared for equality with this map.
     * @return <tt>true</tt> if the specified object is equal to this map.
     * @see Object#equals(Object)
     */
	public boolean equals(Object o) {
		if (o == this) {
			return true;
		} else if (o instanceof FixedMap) {
			FixedMap<?,?> m = (FixedMap<?,?>) o;
			if (m.size() != size())
				return false;
			for(int i = 0; i < keys.length; i++) {
				if (keys[i] != m.keys[i] || values[i] != m.values[i])
					return false;
			}
			return true;
		} else if (o instanceof Map) {
			Map<?,?> m = (Map<?,?>)o;
			return entrySet().equals(m.entrySet());
		} else {
			return false;  // o is not a Map
		}
	}

	private class Entry implements Map.Entry<K, V> {
		int index;
		Entry(int index) {
			this.index = index;
		}
		@SuppressWarnings("unchecked")
		public final K getKey() { return (K)keys[index];	}

		@SuppressWarnings("unchecked")
		public final V getValue() { return (V)values[index]; }

		public V setValue(V value) { throw new UnsupportedOperationException();	}

		public int hashCode() {
			return System.identityHashCode(keys[index]) ^ System.identityHashCode(values[index]);
		}
		
		public boolean equals(Object o) {
			if (o instanceof Map.Entry) {
				final Map.Entry<?,?> e = (Map.Entry<?,?>) o;
				return keys[index] == e.getKey() && values[index] == e.getValue();
			} else return false;
		}
		public String toString() {
			return keys[index] + "=" + values[index];
		}
	}

	private final class EntryIterator extends Entry implements Iterator<Map.Entry<K, V>> {
		int next = 0;
		EntryIterator() { super(-1); }
		@SuppressWarnings("unchecked")
		public V setValue(V value) {
			final V oldValue = (V) values[index];
			values[index] = value;
			return oldValue;
		}
		public boolean hasNext() {	return next < keys.length; }

		public Map.Entry<K, V> next() {
			if (!hasNext()) throw new NoSuchElementException();
			index = next++;
			return this;
		}
		public int hashCode() {	return index < 0 ? System.identityHashCode(this) : super.hashCode(); }
		public boolean equals(Object o) { return index < 0 ? this==o : super.equals(o); }
		public void remove() {	throw new UnsupportedOperationException(); }
		public String toString() { return index < 0 ? "[]" : super.toString(); }
	}
}
