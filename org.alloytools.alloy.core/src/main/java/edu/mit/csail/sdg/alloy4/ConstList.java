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
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.RandomAccess;

/**
 * Immutable; implements a list based on equals(); null values are allowed.
 *
 * @param <T> - the type of element
 */

public final class ConstList<T> extends AbstractList<T> implements Serializable, RandomAccess {

    /**
     * Mutable; this implements a modifiable list that can be used to construct a
     * ConstList; null values are allowed.
     *
     * @param <T> - the type of element
     */
    public static final class TempList<T> {

        /** The underlying list. */
        private final ArrayList<T> list;

        /** Nonnull iff this list is no longer modifiable. */
        private ConstList<T>       clist;

        /** Construct an empty TempList. */
        public TempList() {
            list = new ArrayList<T>();
        }

        /**
         * Construct an empty TempList with initial capacity of n (if n<=0, the list
         * will be given a default capacity of 0)
         */
        public TempList(int n) {
            list = new ArrayList<T>(n >= 0 ? n : 0);
        }

        /**
         * Construct a new TempList whose initial content is n references to the given
         * elem (if n<=0, the created list is empty)
         */
        public TempList(int n, T elem) {
            list = new ArrayList<T>(n > 0 ? n : 0);
            while (n > 0) {
                list.add(elem);
                n--;
            }
        }

        /**
         * Construct a new TempList whose initial content is equal to the given
         * collection.
         */
        public TempList(Collection< ? extends T> all) {
            list = new ArrayList<T>(all);
        }

        /**
         * Construct a new TempList whose initial content is equal to the given array.
         */
        public TempList(T... all) {
            list = new ArrayList<T>(all.length);
            for (int i = 0; i < all.length; i++)
                list.add(all[i]);
        }

        /** Returns a String representation. */
        @Override
        public String toString() {
            return list.toString();
        }

        /** Throws an exception if the list is now unmodifiable. */
        private void chk() {
            if (clist != null)
                throw new UnsupportedOperationException();
        }

        /** Returns the size of the list. */
        public int size() {
            return list.size();
        }

        /** Returns true if the element is in the list. */
        public boolean contains(T elem) {
            return list.contains(elem);
        }

        /** Returns the i-th element. */
        public T get(int index) {
            return list.get(index);
        }

        /** Removes then returns the i-th element. */
        public T remove(int index) {
            chk();
            return list.remove(index);
        }

        /** Removes every element, then return itself. */
        public TempList<T> clear() {
            chk();
            list.clear();
            return this;
        }

        /**
         * Appends the given element to the list, then return itself.
         */
        public TempList<T> add(T elem) {
            chk();
            list.add(elem);
            return this;
        }

        /**
         * Appends the elements in the given collection to the list, then return itself.
         */
        public TempList<T> addAll(Iterable< ? extends T> all) {
            chk();
            if (all instanceof Collection)
                list.addAll((Collection< ? extends T>) all);
            else if (all != null) {
                for (T x : all)
                    list.add(x);
            }
            return this;
        }

        /**
         * Changes the i-th element to be the given element, then return itself.
         */
        public TempList<T> set(int index, T elem) {
            chk();
            list.set(index, elem);
            return this;
        }

        /**
         * Makes this TempList unmodifiable, then construct a ConstList backed by this
         * TempList.
         */
        @SuppressWarnings("unchecked" )
        public ConstList<T> makeConst() {
            if (clist == null)
                clist = (list.isEmpty() ? emptylist : new ConstList<T>(list));
            return clist;
        }
    }

    /** This ensures this class can be serialized reliably. */
    private static final long      serialVersionUID = 0;

    /** The underlying unmodifiable list. */
    private final List<T>          list;

    /** This caches an unmodifiable empty list. */
    @SuppressWarnings("unchecked" )
    private static final ConstList emptylist        = new ConstList(new ArrayList<Object>(0));

    /**
     * Construct a ConstList with the given list as its backing store.
     */
    private ConstList(List<T> list) {
        this.list = list;
    }

    /** Return an unmodifiable empty list. */
    @SuppressWarnings("unchecked" )
    public static <T> ConstList<T> make() {
        return emptylist;
    }

    /**
     * Return an unmodifiable list consisting of "n" references to "elem". (If n<=0,
     * we'll return an unmodifiable empty list)
     */
    public static <T> ConstList<T> make(int n, T elem) {
        if (n <= 0)
            return make();
        ArrayList<T> ans = new ArrayList<T>(n);
        while (n > 0) {
            ans.add(elem);
            n--;
        }
        return new ConstList<T>(ans);
    }

    /**
     * Return an unmodifiable list with the same elements as the given collection.
     * (If collection==null, we'll return an unmodifiable empty list)
     */
    public static <T> ConstList<T> make(Iterable<T> collection) {
        if (collection == null)
            return make();
        if (collection instanceof ConstList)
            return (ConstList<T>) collection;
        if (collection instanceof Collection) {
            Collection<T> col = (Collection<T>) collection;
            if (col.isEmpty())
                return make();
            else
                return new ConstList<T>(new ArrayList<T>(col));
        }
        ArrayList<T> ans = null;
        for (T x : collection) {
            if (ans == null)
                ans = new ArrayList<T>();
            ans.add(x);
        }
        if (ans == null)
            return make();
        else
            return new ConstList<T>(ans);
    }

    /**
     * Returns the i-th element
     *
     * @throws ArrayIndexOutOfBoundsException if the given index doesn't exist
     */
    @Override
    public T get(int index) {
        return list.get(index);
    }

    /** Returns the number of elements in this list. */
    @Override
    public int size() {
        return list.size();
    }
}
