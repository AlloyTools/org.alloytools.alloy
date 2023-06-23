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
 * A Stack implementation based on a singly linked list.
 * @author Emina Torlak
 */
public final class LinkedStack<T> extends  Stack<T> {
	private StackEntry<T> head;
	private int size;
	
	/**
	 * Constructs an empty stack.
	 * @ensures no this.elems'
	 */
	public LinkedStack() {
		head = null;
		size = 0;
	}

	/**
	 * @see kodkod.util.collections.Stack#size()
	 */
	public int size() { return size; }
	
	/**
	 * Pushes an item onto the top of this stack and returns it. 
	 * @ensures this.size' = this.size + 1 && this.elems'[0] = item &&
	 *          all i: [0..this.size) | this.elems'[i+1] = this.elems[i]
	 * @return item
	 */
	public T push(T item) {
		head = new StackEntry<T>(item, head);
		size++;
		return item;
	}
	
	/**
	 * Removes the object at the top of this stack and returns that object as the value of this function.
	 * @ensures this.size' = this.size - 1 && 
	 *          all i: [1..this.size) | this.elems'[i-1] = this.elems[i]
	 * @return this.elems[0]
	 * @throws EmptyStackException  no this.elems
	 */
	public T pop() {
		if (head==null) throw new EmptyStackException();
		final T pop = head.data;
		head = head.next;
		size--;
		return pop;
	}
	
	/**
	 * Looks at the object at the top of this stack without removing it from the stack.
	 * @return this.elems[0]
	 * @throws EmptyStackException  no this.elems
	 */
	public T peek() {
		if (head==null) throw new EmptyStackException();
		return head.data;
	}
	
	/**
	 * Returns the 1-based position where an object is on this stack. 
	 * If the object o occurs as an item in this stack, this method 
	 * returns the distance from the top of the stack of the occurrence 
	 * nearest the top of the stack; the topmost item on the stack is 
	 * considered to be at distance 1. The equals method is used to 
	 * compare o to the items in this stack.
	 * @return o in this.elems[int] => min(this.elems.o) + 1, -1
	 */
	public int search(Object o) {
		StackEntry<T> e = head;
		int position = 1;
		while(e != null) {
			if (equal(o, e.data))
				return position;
			e = e.next;
			position++;
		}
		return -1;
	}
	
	/**
	 * Returns true if the stack is empty; otherwise returns false.
	 * @return no this.elems
	 */
	public boolean empty() { return head == null; }
	
	/**
	 * Iterates over the items in this LinkedStack, starting
	 * at the top of the stack and working its way down.
	 * @return iterator over the elements in this stack.
	 */
	public Iterator<T> iterator() {
		return new Iterator<T>() {
			private StackEntry<T> cursor = head, prev = null, pprev = null;
			public boolean hasNext() {
				return cursor != null;
			}

			public T next() {
				if (cursor==null) throw new NoSuchElementException();
				pprev = prev;
				prev = cursor;
				cursor = cursor.next;
				return prev.data;
			}

			public void remove() {
				if (prev==pprev) {
					throw new UnsupportedOperationException();
				} else if (prev==head) {
					head = cursor;
				} else {
					pprev.next = cursor;
					prev.next = null;
				}
				prev = pprev;
				size--;
			}
			
		};
	}
	
	/**
	 * Represents a stack entry. 
	 * @specfield data: T
	 * @specfield next: StackEntry<T>
	 */
	private static final class StackEntry<T> {
		T data;
		StackEntry<T> next;
		
		StackEntry(T data, StackEntry<T> next) {
			this.data = data;
			this.next = next;
		}
	}

	
}
