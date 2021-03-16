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
 * A mutable IndexedEntry. This class provides various convience method for
 * changing the entry state.
 *
 * @author Emina Torlak
 */
class EntryView<V> implements IndexedEntry<V> {

    private int index;
    private V   value;

    /**
     * Constructs a new entry view with the given index and value.
     *
     * @ensures this.index' = index and this.value' = value
     */
    EntryView(int index, V value) {
        this.index = index;
        this.value = value;
    }

    /**
     * Sets this.index to the given index, and returns the old index.
     *
     * @ensures this.index' = newIndex
     * @return this.index
     */
    int setIndex(int newIndex) {
        final int oldIndex = this.index;
        this.index = newIndex;
        return oldIndex;
    }

    /**
     * Sets this.value to the given value, and returns the old value.
     *
     * @ensures this.value' = newValue
     * @return this.value
     */
    V setValue(V newValue) {
        final V oldValue = this.value;
        this.value = newValue;
        return oldValue;
    }

    /**
     * Sets this.index and this.value to the given index and value, and returns
     * this.
     *
     * @ensures this.index' = newIndex && this.value' = newValue
     * @return this
     */
    IndexedEntry<V> setView(int newIndex, V newValue) {
        this.index = newIndex;
        this.value = newValue;
        return this;
    }

    /**
     * Sets this.index to the given index, and returns this.
     *
     * @ensures this.index' = newIndex
     * @return this
     */
    IndexedEntry<V> setIndexView(int newIndex) {
        this.index = newIndex;
        return this;
    }

    /**
     * Sets this.value to the given value, and returns this.
     *
     * @ensures this.value' = newValue
     * @return this
     */
    IndexedEntry<V> setValueView(V newValue) {
        this.value = newValue;
        return this;
    }

    /**
     * @see kodkod.util.ints.IndexedEntry#index()
     */
    @Override
    public int index() {
        return index;
    }

    /**
     * @see kodkod.util.ints.IndexedEntry#value()
     */
    @Override
    public V value() {
        return value;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public final String toString() {
        return index + "=" + value;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public final boolean equals(Object o) {
        if (o == this)
            return true;
        if (!(o instanceof IndexedEntry))
            return false;
        return AbstractSparseSequence.equal(this, (IndexedEntry< ? >) o);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public final int hashCode() {
        return AbstractSparseSequence.hashCode(this);
    }
}
