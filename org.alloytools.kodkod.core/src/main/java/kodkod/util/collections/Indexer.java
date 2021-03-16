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

/**
 * An index generator for a set of keys. An indexer maps each key in its keyset
 * to a unique integer in the range [0..#keys)
 *
 * @specfield keys: set K
 * @specfield indices: keys lone->one [0..#keys)
 * @author Emina Torlak
 */
public interface Indexer<K> {

    /**
     * Returns the index of the given key, if it is in this.keys. Otherwise returns
     * a negative number.
     *
     * @return key in this.keys => this.indices[key], {i: int | i < 0 }
     */
    public abstract int indexOf(K key);

    /**
     * Returns the key at the given index.
     *
     * @return this.indices.index
     * @throws IndexOutOfBoundsException index !in this.indices[this.keys]
     */
    public abstract K keyAt(int index);

    /**
     * Returns the number of keys in this.indexer.
     *
     * @return #this.keys
     */
    public abstract int size();

}
