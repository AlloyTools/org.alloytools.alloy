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
 * An implementation of a sparse sequence based on an array. This implementation
 * can be used only when the indices of the sequence are known in advance. The
 * indices with which an ArraySequence is construct remain fixed throughout. The
 * put operation fails whenever its index argument is not one of the sequence's
 * pre-set indices, and iteration time is proportional to the number of pre-set
 * indices. This sequence does not allow null values. The lookup and put
 * operations are logarithmic in the number of pre-set indices.
 *
 * @specfield indeces: set int
 * @specfield entries: indeces -> lone (V - null)
 * @author Emina Torlak
 */
public final class ArraySequence<V> extends AbstractSparseSequence<V> implements Cloneable {

    private final EntryView<V>[] entries;
    private int                  size;

    /**
     * Constructs an array sequence that contains the given indeces.
     *
     * @ensures this.indeces' = indeces && no this.entries'
     * @throws NullPointerException indeces = null
     */
    @SuppressWarnings("unchecked" )
    public ArraySequence(IntSet indices) {
        this.entries = new EntryView[indices.size()];
        this.size = indices.size();
        final IntIterator indexIter = indices.iterator();
        for (int i = 0; indexIter.hasNext(); i++) {
            entries[i] = new EntryView<V>(indexIter.next(), null);
        }
    }

    /**
     * Constructs a new array sequence with the same index/value mappings as the
     * given sequence.
     *
     * @ensures this.entries' = s.entries
     * @throws NullPointerException s = null || null in s
     */
    @SuppressWarnings("unchecked" )
    public ArraySequence(SparseSequence< ? extends V> s) {
        this.entries = new EntryView[s.size()];
        this.size = s.size();
        int i = 0;
        for (IndexedEntry< ? > entry : s) {
            if (entry.value() == null)
                throw new NullPointerException();
            entries[i++] = new EntryView<V>(entry.index(), (V) entry.value());
        }
    }

    /**
     * Copy constructor.
     *
     * @ensures constructs a deep copy of the original array sequence.
     */
    @SuppressWarnings("unchecked" )
    private ArraySequence(ArraySequence<V> original) {
        this.size = original.size;
        this.entries = new EntryView[original.entries.length];
        int i = 0;
        for (EntryView<V> e : original.entries)
            this.entries[i++] = new EntryView<V>(e.index(), e.value());
    }

    /**
     * Returns the number of entries in this sequence.
     *
     * @return #this.entries
     * @see kodkod.util.ints.SparseSequence#size()
     */
    @Override
    public int size() {
        return size;
    }

    /**
     * Returns true if this sequence is empty; otherwise returns false.
     *
     * @return no this.entries
     * @see kodkod.util.ints.SparseSequence#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.util.ints.SparseSequence#clear()
     */
    @Override
    public void clear() {
        for (EntryView<V> e : entries) {
            e.setValue(null);
        }
    }

    /**
     * Searches this.entries for the specified index using the binary search
     * algorithm. If the index is not found, then -insertionPoint - 1 is returned,
     * where insertionPoint is the point at which the given index would be inserted
     * into this.entries.
     *
     * @return the position in this.entries where the entry with the given index is
     *         located, or -insertionPoint - 1 if the index is not in this.indeces
     */
    private final int search(int index) {
        int low = 0;
        int high = entries.length - 1;

        while (low <= high) {
            int mid = (low + high) >>> 1;
            int midIndex = entries[mid].index();
            if (midIndex < index)
                low = mid + 1;
            else if (midIndex > index)
                high = mid - 1;
            else
                return mid; // key found
        }

        return -(low + 1); // key not found.
    }

    /**
     * Puts the given value at the specified index. If the sequence already mapped
     * the index to a value, the previous value is replaced with the new one and
     * returned.
     *
     * @ensures this.entries' = this.entries + index->value
     * @return this.entries[index]
     * @throws IndexOutOfBoundsException index !in this.indeces
     * @throws NullPointerException value = null
     * @see kodkod.util.ints.SparseSequence#put(int, Object)
     */
    @Override
    public V put(int index, V value) {
        if (value == null)
            throw new NullPointerException();
        final int position = search(index);
        if (position < 0)
            throw new IndexOutOfBoundsException("" + index);
        if (entries[position] == null)
            size++;
        return entries[position].setValue(value);
    }

    /**
     * Returns the value to which this sequence maps the given index. If the index
     * is not mapped, null is returned.
     *
     * @return this.entries[index]
     * @see kodkod.util.ints.SparseSequence#get(int)
     */
    @Override
    public V get(int index) {
        final int position = search(index);
        return position < 0 ? null : entries[position].value();
    }

    /**
     * Removes the entry with the given index, if it exists, and returns the value
     * previously stored at the index. If the sequence had no previous mapping for
     * the index, null is returned.
     *
     * @ensures this.entries' = this.entries - index->E
     * @return this.entries[index]
     * @see kodkod.util.ints.SparseSequence#remove(int)
     */
    @Override
    public V remove(int index) {
        final int position = search(index);
        if (position < 0)
            return null;
        else {
            if (entries[position].value() != null)
                size--;
            return entries[position].setValue(null);
        }
    }

    /**
     * Returns true if this sparse sequence has an entry for the given index;
     * otherwise returns false.
     *
     * @return index in this.indeces
     * @see kodkod.util.ints.SparseSequence#containsIndex(int)
     */
    @Override
    public boolean containsIndex(int index) {
        final int position = search(index);
        return position >= 0 && entries[position].value() != null;
    }

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
     * @see kodkod.util.ints.SparseSequence#iterator(int, int)
     */
    @Override
    public Iterator<IndexedEntry<V>> iterator(int from, int to) {
        return from <= to ? new AscendingIterator(from, to) : new DescendingIterator(from, to);
    }

    /**
     * Returns the entry with the smallest index. If the sequence is empty, returns
     * null.
     *
     * @return {e: IndexedEntry | e.index = min(this.entries.E) && e.value =
     *         this.entries[e.index] }
     * @see kodkod.util.ints.SparseSequence#first()
     */
    @Override
    public IndexedEntry<V> first() {
        if (size == 0)
            return null;
        for (EntryView<V> e : entries) {
            if (e.value() != null)
                return e;
        }
        throw new InternalError(); // unreachable code
    }

    /**
     * Returns the entry with the largest index. If the sequence is empty, returns
     * null.
     *
     * @return {e: IndexedEntry | e.index = max(this.entries.E) && e.value =
     *         this.entries[e.index] }
     * @see kodkod.util.ints.SparseSequence#last()
     */
    @Override
    public IndexedEntry<V> last() {
        if (size == 0)
            return null;
        for (int i = entries.length - 1; i >= 0; i--) {
            if (entries[i].value() != null)
                return entries[i];
        }
        throw new InternalError(); // unreachable code
    }

    /**
     * If an entry for the given index exists, it is returned. Otherwise,
     * successor(index) is returned.
     *
     * @return this.containsIndex(index) => {e: IndexedEntry | e.index = index &&
     *         e.value = this.entries[index] }, successor(index)
     * @see kodkod.util.ints.SparseSequence#ceil(int)
     */
    @Override
    public IndexedEntry<V> ceil(int index) {
        final int position = search(index);
        for (int i = position < 0 ? -position - 1 : position; i < entries.length; i++) {
            if (entries[i].value() != null)
                return entries[i];
        }
        return null;
    }

    /**
     * If an entry for the given index exists, it is returned. Otherwise,
     * predecessor(index) is returned.
     *
     * @return this.containsIndex(index) => {e: IndexedEntry | e.index = index &&
     *         e.value = this.entries[index] }, predecessor(index)
     * @see kodkod.util.ints.SparseSequence#floor(int)
     */
    @Override
    public IndexedEntry<V> floor(int index) {
        final int position = search(index);
        for (int i = position < -1 ? -position - 2 : position; i >= 0; i--) {
            if (entries[i].value() != null)
                return entries[i];
        }
        return null;
    }

    /**
     * Returns a copy of this sparse sequence. The copy is independent of this
     * sequence.
     *
     * @return a copy of this sparse sequence.
     * @see kodkod.util.ints.SparseSequence#clone()
     */
    @Override
    public ArraySequence<V> clone() {
        return new ArraySequence<V>(this);
    }

    /**
     * An iterator that traverses this sequence in the ascending order.
     *
     * @author Emina Torlak
     */
    private final class AscendingIterator implements Iterator<IndexedEntry<V>> {

        final int       endIndex;
        IndexedEntry<V> lastReturned = null;
        int             cursor;

        /**
         * @requires from <= to
         */
        AscendingIterator(int from, int to) {
            final int fromPos = search(from);
            final int toPos = search(to);
            cursor = fromPos < 0 ? -fromPos - 1 : fromPos;
            endIndex = toPos < -1 ? -toPos - 2 : toPos;
        }

        @Override
        public boolean hasNext() {
            while (cursor < entries.length && entries[cursor].value() == null)
                cursor++;
            return cursor <= endIndex;
        }

        @Override
        public IndexedEntry<V> next() {
            if (!hasNext())
                throw new NoSuchElementException();
            return lastReturned = entries[cursor++];
        }

        @Override
        public void remove() {
            if (lastReturned == null)
                throw new IllegalStateException();
            entries[lastReturned.index()].setValue(null);
            lastReturned = null;
        }
    }

    /**
     * An iterator that traverses this sequence in the descending order.
     *
     * @author Emina Torlak
     */
    private final class DescendingIterator implements Iterator<IndexedEntry<V>> {

        final int       endIndex;
        IndexedEntry<V> lastReturned = null;
        int             cursor;

        /**
         * @requires from >= to
         */
        DescendingIterator(int from, int to) {
            final int fromPos = search(from);
            final int toPos = search(to);
            cursor = fromPos < -1 ? -fromPos - 2 : fromPos;
            endIndex = toPos < 0 ? -toPos - 1 : toPos;
        }

        @Override
        public boolean hasNext() {
            while (cursor >= 0 && entries[cursor].value() == null)
                cursor--;
            return cursor >= endIndex;
        }

        @Override
        public IndexedEntry<V> next() {
            if (!hasNext())
                throw new NoSuchElementException();
            return lastReturned = entries[cursor--];
        }

        @Override
        public void remove() {
            if (lastReturned == null)
                throw new IllegalStateException();
            entries[lastReturned.index()].setValue(null);
            lastReturned = null;
        }

    }

}
