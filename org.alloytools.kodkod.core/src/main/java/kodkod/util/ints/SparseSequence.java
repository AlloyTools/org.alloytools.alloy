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

import java.util.Collection;
import java.util.Iterator;

/**
 * <p>
 * Represents a sparse sequence -- a sequence whose indices are not necessarily
 * contiguous. For example, a sparse sequence can have elements at indices 10,
 * 2121, and 3000, without having any elements in between. This specification of
 * sparse sequences also supports negative indeces. Formally, the following
 * methods specify a partial function from integers to values of type V.
 * </p>
 * <p>
 * Sequence implementations are not required to support mutation. All mutating
 * operations are optional and may throw an UnsupportedOperationException.
 * </p>
 *
 * @specfield entries: int -> lone V
 * @author Emina Torlak
 */
public interface SparseSequence<V> extends Iterable<IndexedEntry<V>> {

    /**
     * Returns the number of entries in this sequence.
     *
     * @return #this.entries
     */
    public abstract int size();

    /**
     * Returns true if this sequence is empty; otherwise returns false.
     *
     * @return no this.entries
     */
    public abstract boolean isEmpty();

    /**
     * Removes all entries from this sequences.
     *
     * @ensures no this.entries'
     */
    public abstract void clear();

    /**
     * Puts the given value at the specified index. If the sequence already mapped
     * the index to a value, the previous value is replaced with the new one and
     * returned.
     *
     * @ensures this.entries' = this.entries + index->value
     * @return this.entries[index]
     * @throws IndexOutOfBoundsException the given index is not valid for this
     *             sequence.
     * @throws IllegalArgumentException the given value cannot be stored in this
     *             sequence.
     */
    public abstract V put(int index, V value);

    /**
     * Copies all of the entries from the specified sparse sequence to this
     * sequence. The effect of this call is equivalent to that of calling
     * put(e.index, e.value) on this sequence once for each entry e in the specified
     * sequence.
     *
     * @ensures this.entries' = this.entries ++ s.entries
     * @throws IndexOutOfBoundsException s contains indeces that are not valid for
     *             this sequence.
     * @throws IllegalArgumentException s contains a value that cannot be stored in
     *             this sequence.
     */
    public abstract void putAll(SparseSequence< ? extends V> s);

    /**
     * Returns the value to which this sequence maps the given index. If the index
     * is not mapped, null is returned.
     *
     * @return this.entries[index]
     */
    public abstract V get(int index);

    /**
     * Removes the entry with the given index, if it exists, and returns the value
     * previously stored at the index. If the sequence had no previous mapping for
     * the index, null is returned.
     *
     * @ensures this.entries' = this.entries - index->E
     * @return this.entries[index]
     */
    public abstract V remove(int index);

    /**
     * Returns true if this sparse sequence has an entry for the given index;
     * otherwise returns false.
     *
     * @return some this.entries[index]
     */
    public abstract boolean containsIndex(int index);

    /**
     * Returns the set of all indices mapped by this sparse sequence. The returned
     * set supports removal iff this is not an unmodifiable sparse sequence. The
     * returned set may be uncloneable.
     *
     * @return {s: IntSet | s.ints = this.entries.V}
     */
    public abstract IntSet indices();

    /**
     * Returns true if this sequence has an entry with the given value; otherwise
     * returns false.
     *
     * @return some this.entries.value
     */
    public abstract boolean contains(Object value);

    /**
     * Returns a Collection view of the values stored in this sequence. The returned
     * collection supports removal iff this is not an unmodifiable sparse sequence.
     *
     * @return {c: Collection | c.size()=this.size() && all v: V | c.contains(v) <=>
     *         this.contains(v) }
     */
    public abstract Collection<V> values();

    /**
     * Returns an iterator over the entries in this sequence in the ascending order
     * of indeces, starting at this.first().
     *
     * @return an iterator over this.entries starting at the entry with the smallest
     *         index
     */
    @Override
    public abstract Iterator<IndexedEntry<V>> iterator();

    /**
     * Returns an iterator over the entries in this sequence, whose indeces are
     * between from and to. If from < to, the entries are returned in the ascending
     * order of indeces. Otherwise, they are returned in the descending order of
     * indeces.
     *
     * @return an iterator over the entries in this sequence whose indeces are
     *         between from and to. Formally, if from < to, then the first and last
     *         entries returned by the iterator are this.ceil(from) and
     *         this.floor(to). Otherwise, they are this.floor(from) and
     *         this.ceil(to).
     */
    public abstract Iterator<IndexedEntry<V>> iterator(int from, int to);

    /**
     * Returns the entry with the smallest index. If the sequence is empty, returns
     * null.
     *
     * @return {e: IndexedEntry | e.index = min(this.entries.E) && e.value =
     *         this.entries[e.index] }
     */
    public abstract IndexedEntry<V> first();

    /**
     * Returns the entry with the largest index. If the sequence is empty, returns
     * null.
     *
     * @return {e: IndexedEntry | e.index = max(this.entries.E) && e.value =
     *         this.entries[e.index] }
     */
    public abstract IndexedEntry<V> last();

    /**
     * If an entry for the given index exists, it is returned. Otherwise,
     * successor(index) is returned.
     *
     * @return this.containsIndex(index) => {e: IndexedEntry | e.index = index &&
     *         e.value = this.entries[index] }, successor(index)
     */
    public abstract IndexedEntry<V> ceil(int index);

    /**
     * If an entry for the given index exists, it is returned. Otherwise,
     * predecessor(index) is returned.
     *
     * @return this.containsIndex(index) => {e: IndexedEntry | e.index = index &&
     *         e.value = this.entries[index] }, predecessor(index)
     */
    public abstract IndexedEntry<V> floor(int index);

    /**
     * Compares the specified object with this sequence for equality. Returns true
     * if the given object is also a sparse sequence and the two sequences have the
     * same entries. More formally, two sequences t1 and t2 have the the same
     * entries if they represent the same function from integers to values: i.e.
     * t1.entries = t2.entries. This ensures that the equals method works properly
     * across different implementations of the SparseSequence interface.
     *
     * @return o in SparseSequence && o.entries = this.entries
     */
    @Override
    public abstract boolean equals(Object o);

    /**
     * Returns the hash code value for this sparse sequence. A hash function for a
     * sparse sequence must ensure that t1.equals(t2) implies that
     * t1.hashCode()==t2.hashCode() for any two sequences t1 and t2, as required by
     * the general contract of Object.hashCode.
     *
     * @return hash code for this sparse sequence
     */
    @Override
    public abstract int hashCode();

    /**
     * Returns a copy of this sparse sequence. The copy is independent of this
     * sequence unless this is a singleton or immutable, in which case clone() may
     * return this. An implementing class that does not support cloning may throw a
     * CloneNotSupportedException.
     *
     * @return a copy of this sparse sequence.
     * @throws CloneNotSupportedException this is not cloneable
     */
    public abstract SparseSequence<V> clone() throws CloneNotSupportedException;

}
