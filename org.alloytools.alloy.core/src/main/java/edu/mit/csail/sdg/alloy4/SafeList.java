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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import edu.mit.csail.sdg.alloy4.ConstList.TempList;

/**
 * This list allows add() but disallows remove() and set(); null values are
 * allowed.
 * <p>
 * By making this sacrifice, we are able to provide a very cheap "duplicate
 * method" that simulates making a copy without actually making a copy.
 * <p>
 * Furthermore, this class's iterator allows concurrent insertion and iteration
 * (that is, we can iterate over the list while adding elements to the list at
 * the same time). The iterator is guaranteed to iterate over exactly the
 * elements that existed at the time that the iterator was created.
 * <p>
 * <b>Thread Safety:</b> Safe.
 *
 * @param <T> - the type of element
 */

public final class SafeList<T> implements Serializable, Iterable<T> {

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * The actual list of elements; it will be shared by an original SafeList and
     * all its unmodifiable copies.
     */
    private final List<T>     list;

    /**
     * If negative, that means this instance is mutable; otherwise, it is the list
     * size at the time of the copy.
     */
    private final int         max;

    /** Constructs a modifiable empty list. */
    public SafeList() {
        list = new ArrayList<T>();
        max = (-1);
    }

    /**
     * Constructs a modifiable empty list with the initial capacity.
     */
    public SafeList(int initialCapacity) {
        list = new ArrayList<T>(initialCapacity);
        max = (-1);
    }

    /**
     * Constructs a modifiable list containing the elements from the given
     * collection.
     */
    public SafeList(Collection< ? extends T> initialValue) {
        list = new ArrayList<T>(initialValue);
        max = (-1);
    }

    /**
     * Constructs a modifiable list containing the elements from the given iterable.
     */
    public SafeList(Iterable< ? extends T> initialValue) {
        list = new ArrayList<T>();
        max = (-1);
        for (T obj : initialValue)
            list.add(obj);
    }

    /**
     * Private constructor for assigning exact values to "list" and "max".
     */
    private SafeList(List<T> list, int max) {
        this.list = list;
        this.max = max;
    }

    /**
     * Constructs an unmodifiable copy of an existing SafeList.
     */
    public SafeList<T> dup() {
        synchronized (SafeList.class) {
            return new SafeList<T>(list, size());
        }
    }

    /**
     * Constructs a modifiable ArrayList containing the same elements as this list.
     */
    public List<T> makeCopy() {
        synchronized (SafeList.class) {
            int n = size();
            ArrayList<T> ans = new ArrayList<T>(n);
            for (int i = 0; i < n; i++)
                ans.add(list.get(i));
            return ans;
        }
    }

    /**
     * Constructs an unmodifiable ConstList containing the same elements as this
     * list.
     */
    public ConstList<T> makeConstList() {
        synchronized (SafeList.class) {
            int n = size();
            TempList<T> ans = new TempList<T>(n);
            for (int i = 0; i < n; i++)
                ans.add(list.get(i));
            return ans.makeConst();
        }
    }

    /**
     * Computes a hash code that is consistent with SafeList's equals() and
     * java.util.List's hashCode() methods.
     */
    @Override
    public int hashCode() {
        int answer = 1;
        for (Object obj : this)
            answer = 31 * answer + (obj != null ? obj.hashCode() : 0);
        return answer;
    }

    /**
     * Returns true if (that instanceof List or that instanceof SafeList), and that
     * contains the same elements as this list.
     */
    @SuppressWarnings("unchecked" )
    @Override
    public boolean equals(Object that) {
        if (this == that)
            return true;
        int n;
        Iterator< ? > b;
        if (that instanceof List) {
            n = ((List) that).size();
            if (n != size())
                return false;
            b = ((List) that).iterator();
        } else if (that instanceof SafeList) {
            n = ((SafeList) that).size();
            if (n != size())
                return false;
            b = ((SafeList) that).iterator();
        } else
            return false;
        Iterator< ? > a = iterator();
        for (int i = 0; i < n; i++) { // We must read up to n elements only
            Object aa = a.next(), bb = b.next();
            if (aa == null) {
                if (bb != null)
                    return false;
            } else {
                if (!aa.equals(bb))
                    return false;
            }
        }
        return true;
    }

    /** Returns true if the list contains the given element. */
    public boolean contains(Object item) {
        for (T entry : this) {
            if (entry == null) {
                if (item == null)
                    return true;
            } else {
                if (entry.equals(item))
                    return true;
            }
        }
        return false;
    }

    /** Add an element into the list. */
    public boolean add(T item) {
        synchronized (SafeList.class) {
            if (max >= 0)
                throw new UnsupportedOperationException();
            else
                return list.add(item);
        }
    }

    /** Add a collection of elements into the list. */
    public void addAll(Collection< ? extends T> items) {
        synchronized (SafeList.class) {
            if (max >= 0)
                throw new UnsupportedOperationException();
            list.addAll(items);
        }
    }

    /** Get an element from the list. */
    public T get(int i) {
        synchronized (SafeList.class) {
            if (max >= 0 && i >= max)
                throw new IndexOutOfBoundsException();
            else
                return list.get(i);
        }
    }

    /** Returns the size of the list. */
    public int size() {
        synchronized (SafeList.class) {
            if (max >= 0)
                return max;
            else
                return list.size();
        }
    }

    /** Returns true if the list is empty. */
    public boolean isEmpty() {
        return size() == 0;
    }

    /**
     * Returns an iterator that iterates over elements in this list (in the order
     * that they were inserted).
     * <p>
     * Note: This iterator's remove() method always throws
     * UnsupportedOperationException.
     * <p>
     * Note: This iterator always returns exactly the list of elements that existed
     * at the time that the iterator was created (even if the list is modified after
     * that point).
     */
    @Override
    public Iterator<T> iterator() {
        synchronized (SafeList.class) {
            return new Iterator<T>() {

                private final int imax = (max >= 0 ? max : list.size());
                private int       now  = 0;

                @Override
                public final T next() {
                    if (now >= imax)
                        throw new NoSuchElementException();
                    synchronized (SafeList.class) {
                        T answer = list.get(now);
                        now++;
                        return answer;
                    }
                }

                @Override
                public final boolean hasNext() {
                    return now < imax;
                }

                @Override
                public final void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        }
    }

    /** Returns a String representation of this list. */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("[");
        boolean first = true;
        for (Object x : this) {
            if (first)
                first = false;
            else
                sb.append(", ");
            if (x == this)
                sb.append("(this collection)");
            else
                sb.append(x);
        }
        return sb.append(']').toString();
    }
}
