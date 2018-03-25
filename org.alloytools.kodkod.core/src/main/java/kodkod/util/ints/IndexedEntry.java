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
 * An entry in a {@link SparseSequence sparse sequence}.
 *
 * @specfield index: int
 * @specfield value: E
 * @author Emina Torlak
 */
public interface IndexedEntry<E> {

    /**
     * Returns the index of this entry.
     *
     * @return this.index
     */
    public abstract int index();

    /**
     * Returns the value stored in this entry.
     *
     * @return this.value
     */
    public abstract E value();

    /**
     * Compares the specified object with this entry for equality. Returns true if
     * the given object is also an indexed entry and the two entries have the same
     * indeces and values. More formally, two entries e1 and e2 are equal if
     * e1.index = e2.index && e1.value = e2.value. This ensures that the equals
     * method works properly across different implementations of the IndexedEntry
     * interface.
     *
     * @return o in IndexedEntry && o.index = this.index && o.value = this.value
     */
    @Override
    public abstract boolean equals(Object o);

    /**
     * Returns the hash code value for this indexed entry. The hash code of an
     * indexed entry e is defined to be: e.index ^ (e.value=null ? 0 :
     * e.value.hashCode()). This ensures that e1.equals(e2) implies that
     * e1.hashCode()==e2.hashCode() for any two IndexedEntries e1 and e2, as
     * required by the general contract of Object.hashCode.
     */
    @Override
    public abstract int hashCode();
}
