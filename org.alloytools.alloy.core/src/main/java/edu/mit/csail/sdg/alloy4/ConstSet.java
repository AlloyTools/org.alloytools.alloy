/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.io.Serializable;
import java.util.AbstractSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Immutable; implements a set based on hashCode() and equals(); null value is
 * allowed.
 *
 * @param <K> - the type of element
 */

public final class ConstSet<K> extends AbstractSet<K> implements Serializable {

    /** This ensures this class can be serialized reliably. */
    private static final long             serialVersionUID = 0;

    /** The underlying Collections.unmodifiableSet set. */
    private final Set<K>                  set;

    /** This caches a readonly empty Set. */
    private static final ConstSet<Object> emptyset         = new ConstSet<Object>(new HashSet<Object>(0));

    /**
     * Constructs an unmodifiable map with the given set as the backing store.
     */
    private ConstSet(Set< ? extends K> set) {
        this.set = Collections.unmodifiableSet(set);
    }

    /** Returns an unmodifiable empty set. */
    @SuppressWarnings("unchecked" )
    public static <K> ConstSet<K> make() {
        return (ConstSet<K>) emptyset;
    }

    /**
     * Returns an unmodifiable set with the same elements and traversal order as the
     * given set. (If set==null, we'll return an unmodifiable empty set)
     */
    public static <K> ConstSet<K> make(Iterable<K> collection) {
        if (collection instanceof ConstSet)
            return (ConstSet<K>) collection;
        LinkedHashSet<K> ans = null;
        if (collection != null)
            for (K element : collection) {
                if (ans == null)
                    ans = new LinkedHashSet<K>();
                ans.add(element);
            }
        if (ans == null)
            return make();
        else
            return new ConstSet<K>(ans);
    }

    /** Returns the number of objects in this set. */
    @Override
    public int size() {
        return set.size();
    }

    /** Returns a read-only iterator over this set. */
    @Override
    public Iterator<K> iterator() {
        return set.iterator();
    }

    /** Returns true if the given object is in this set. */
    @Override
    public boolean contains(Object element) {
        return set.contains(element);
    } // overridden for performance
}
