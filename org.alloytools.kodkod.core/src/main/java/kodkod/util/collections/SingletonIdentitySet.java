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

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * <p>
 * This is an immutable singleton set implementation that tests for membership
 * using reference-equality in place of object-equality when comparing elements.
 * </p>
 *
 * @specfield element: V
 * @author Emina Torlak
 */
public final class SingletonIdentitySet<V> extends AbstractSet<V> {

    private final V element;

    /**
     * Constructs a SingletonIdentitySet that will hold the given element.
     *
     * @ensures this.element' = element
     */
    public SingletonIdentitySet(V element) {
        this.element = element;
    }

    /**
     * Constructs a SingletonIdentitySet that will hold the first element returned
     * by the given collection's iterator.
     *
     * @ensures this.element' = collection.iterator().next()
     * @throws NoSuchElementException collection.isEmpty()
     */
    public SingletonIdentitySet(Collection< ? extends V> collection) {
        this.element = collection.iterator().next();
    }

    /**
     * Returns true iff this.element and obj are the same object.
     *
     * @return this.element == obj
     */
    @Override
    public boolean contains(Object obj) {
        return element == obj;
    }

    /**
     * @see java.util.Set#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection< ? > collection) {
        if (collection.isEmpty())
            return true;
        else if (collection.size() == 1)
            return collection.iterator().next() == this.element;
        else
            return false;
    }

    /**
     * Returns false.
     *
     * @return false.
     */
    @Override
    public boolean isEmpty() {
        return false;
    }

    /**
     * @see java.util.Set#iterator()
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Iterator<V> iterator() {
        return Containers.iterate(this.element);
    }

    /**
     * Returns 1.
     *
     * @return 1
     */
    @Override
    public int size() {
        return 1;
    }

    /**
     * Compares the specified object with this set for equality. Returns
     * <tt>true</tt> if the given object is also a set and the two sets contain
     * identical object-references.
     * <p>
     * <b>Owing to the reference-equality-based semantics of this set it is possible
     * that the symmetry and transitivity requirements of the <tt>Object.equals</tt>
     * contract may be violated if this set is compared to a normal set. However,
     * the <tt>Object.equals</tt> contract is guaranteed to hold among
     * <tt>SingletonHashSet</tt> instances.</b>
     *
     * @return <tt>true</tt> if the specified object is equal to this set.
     * @see Object#equals(Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof Set) {
            final Set< ? > s = (Set< ? >) o;
            return s.size() == 1 && s.iterator().next() == this.element;
        } else {
            return false;
        }
    }

    /**
     * Returns 0 if this.element is null; otherwise returns this.element.hashCode().
     *
     * @return this.element = null ? 0 : this.element.hashCode()
     * @see java.util.AbstractSet#hashCode()
     */
    @Override
    public int hashCode() {
        return this.element == null ? 0 : element.hashCode();
    }
}
