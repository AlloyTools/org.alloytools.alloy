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

/**
 * Immutable; implements a list where it is combine them; null values are NOT
 * allowed.
 */

public final class JoinableList<E> extends AbstractList<E> implements Serializable {

    /** This ensures the class can be serialized reliably. */
    private static final long     serialVersionUID = 0;

    /**
     * The number of items stored in this list.
     * <p>
     * <b>Invariant:</b> count == (pre!=null ? pre.count : 0) + (item!=null ? 1 : 0)
     * + (post!=null ? post.count : 0)
     */
    private final int             count;

    /** The list of items before "this.item"; may be null. */
    private final JoinableList<E> pre;

    /** The list of items after "this.item"; may be null. */
    private final JoinableList<E> post;

    /** If nonnull, it stores an item. */
    private final E               item;

    /** Construct a JoinableList object. */
    private JoinableList(int count, JoinableList<E> pre, E item, JoinableList<E> post) {
        this.count = count;
        this.pre = pre;
        this.item = item;
        this.post = post;
    }

    /** Construct an empty list. */
    public JoinableList() {
        this(0, null, null, null);
    }

    /**
     * Construct a list containing a single item, or return an empty list if
     * item==null.
     */
    public JoinableList(E item) {
        this((item != null ? 1 : 0), null, item, null);
    }

    /**
     * Returns a list that represents the concatenation of this list and that list.
     */
    public JoinableList<E> make(JoinableList<E> that) {
        if (that == null || that.count == 0)
            return this;
        else if (count == 0)
            return that;
        int sum = count + that.count;
        if (sum < count)
            throw new OutOfMemoryError(); // integer overflow
        if (post != null)
            return new JoinableList<E>(sum, this, null, that);
        else
            return new JoinableList<E>(sum, pre, item, that);
    }

    /**
     * Returns a list that represents the result of appending newItem onto this
     * list; if newItem==null we return this list as-is.
     */
    public JoinableList<E> make(E newItem) {
        if (newItem == null)
            return this;
        int sum = count + 1; // integer overflow
        if (sum < 1)
            throw new OutOfMemoryError();
        if (post != null)
            return new JoinableList<E>(sum, this, newItem, null);
        if (item != null)
            return new JoinableList<E>(sum, pre, item, new JoinableList<E>(newItem));
        return new JoinableList<E>(sum, pre, newItem, null);
    }

    /**
     * If the list if nonempty, arbitrarily return one of the item, otherwise throw
     * ArrayIndexOutOfBoundsException.
     */
    public E pick() {
        if (item != null)
            return item;
        else
            return get(0);
    }

    /**
     * Return the i-th element
     *
     * @throws ArrayIndexOutOfBoundsException if the given index doesn't exist
     */
    @Override
    public E get(int i) {
        if (i < 0 || i >= count)
            throw new ArrayIndexOutOfBoundsException();
        JoinableList<E> x = this;
        while (true) {
            int pre = (x.pre == null) ? 0 : x.pre.count;
            if (i < pre) {
                x = x.pre;
                continue;
            }
            if (x.item == null) {
                i = i - pre;
                x = x.post;
            } else if (i != pre) {
                i = i - pre - 1;
                x = x.post;
            } else
                return x.item;
        }
    }

    /** Returns the number of elements in this list. */
    @Override
    public int size() {
        return count;
    }
}
