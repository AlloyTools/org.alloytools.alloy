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

import java.util.EmptyStackException;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A Stack implementation based on an array.
 *
 * @author Emina Torlak
 */
public class ArrayStack<T> extends Stack<T> {

    /*
     * stack elements: the last element in the array is at the top of the stack.
     */
    private T[] elems;
    private int size;

    /**
     * Constructs an empty stack with the inital capacity of 10.
     *
     * @ensures no this.elems'
     */
    public ArrayStack() {
        this(10);
    }

    @SuppressWarnings("unchecked" )
    public ArrayStack(int initialCapacity) {
        if (initialCapacity < 0)
            throw new IllegalArgumentException(initialCapacity + "<0");
        elems = (T[]) new Object[initialCapacity];
        size = 0;
    }

    /**
     * Increases the capacity of this ArrayStack, if necessary, to ensure that it
     * can hold at least the number of elements specified by the minimum capacity
     * argument.
     */
    @SuppressWarnings("unchecked" )
    public void ensureCapacity(int minCapacity) {
        final int oldCapacity = elems.length;
        if (minCapacity > oldCapacity) {
            final T[] oldElems = elems;
            elems = (T[]) new Object[StrictMath.max(minCapacity, (oldCapacity * 3) / 2)];
            System.arraycopy(oldElems, 0, elems, 0, size);
        }
    }

    /**
     * Trims the capacity of this ArrayStack to be the stack's current size. An
     * application can use this operation to minimize the storage of an ArrayStack
     * instance.
     */
    @SuppressWarnings("unchecked" )
    public void trimToSize() {
        final int oldCapacity = elems.length;
        if (size < oldCapacity) {
            final Object oldElems[] = elems;
            elems = (T[]) new Object[size];
            System.arraycopy(oldElems, 0, elems, 0, size);
        }
    }

    /**
     * @see kodkod.util.collections.Stack#size()
     */
    @Override
    public int size() {
        return size;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.util.collections.Stack#push
     */
    @Override
    public T push(T item) {
        ensureCapacity(size + 1);
        elems[size++] = item;
        return item;
    }

    /**
     * @see kodkod.util.collections.Stack#pop()
     */
    @Override
    public T pop() {
        if (empty())
            throw new EmptyStackException();
        final T top = elems[--size];
        elems[size] = null;
        return top;
    }

    /**
     * @see kodkod.util.collections.Stack#peek()
     */
    @Override
    public T peek() {
        if (empty())
            throw new EmptyStackException();
        return elems[size - 1];
    }

    /**
     * @see kodkod.util.collections.Stack#search(java.lang.Object)
     */
    @Override
    public int search(Object o) {
        for (int i = size - 1; i >= 0; i--) {
            if (equal(o, elems[i]))
                return i;
        }
        return -1;
    }

    /**
     * @see kodkod.util.collections.Stack#empty()
     */
    @Override
    public boolean empty() {
        return size == 0;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.util.collections.Stack#iterator()
     */
    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {

            int cursor = size - 1, lastReturned = -1;

            @Override
            public boolean hasNext() {
                return cursor >= 0;
            }

            @Override
            public T next() {
                if (cursor < 0)
                    throw new NoSuchElementException();
                lastReturned = cursor;
                return elems[cursor--];
            }

            @Override
            public void remove() {
                if (lastReturned < 0)
                    throw new UnsupportedOperationException();
                size--;
                System.arraycopy(elems, lastReturned + 1, elems, lastReturned, size - lastReturned);
                elems[size] = null;
                lastReturned = -1;
            }

        };
    }

}
