/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.examples.bmc;

import java.util.HashSet;
import java.util.Set;

/****** List demo ******/

/**
 * Node spec.
 * 
 * @specfield next: Node + null
 * @specfield data: String + null
 * @author Emina Torlak
 *
 */
final class Node {
	String data;
	Node next;

	Node(String data, Node next) {
		this.data = data;
		this.next = next;
	}
}

/**
 * List spec.
 * 
 * @specfield head: Node + null
 * @specfield nodes: set Node + null
 * @invariant nodes = head.*next
 * @invariant no iden & ^(next & nodes -> nodes)
 * @author Emina Torlak
 *
 */
public class List {

	private Node head;

	public List() {
		head = null;
	}

	public void add(String item) {
		head = new Node(item, head);
	}

	public boolean empty() { 
		return head == null; 
	}
	
	/**
	 * @requires this.head != null && this.head.next != null
	 * @modifies next, head
	 * @ensures let ns = this.nodes - null | nodes' = nodes and next' & (ns -> ns) = ~ (next & (ns -> ns))
	 */
	public void reverse(){
		
		Node nearNode = head;
		Node midNode = nearNode.next;
		Node farNode = midNode.next;

		nearNode.next = farNode /* should be null */; 

		while(farNode != null){
			midNode.next = nearNode;
			nearNode = midNode;
			midNode = farNode;
			farNode = farNode.next;
		}

		midNode.next = nearNode;
		head = midNode;		
	}

	/**
	 * @requires this.head != null && this.head.next != null
	 * @modifies next, head
	 * @ensures let ns = nodes - null | nodes' = nodes and next' & (ns -> ns) = ~(next & (ns -> ns))
	 */
	public void reverseFinitized(){
	
		assert this.head != null &&			// assume this.head != null && this.head.next != null
			   this.head.next != null;
		
		Node nearNode = this.head;			// nearNode0 := this.head
		Node midNode = nearNode.next;		// midNode0 := nearNode0.next
		Node farNode = midNode.next;		// farNode0 := midNode0.next

		nearNode.next = farNode; 			// next0 := update(next, nearNode0 -> farNode0)

		if (farNode != null) {				// guard0 := farNode0 != null
			midNode.next = nearNode;		// next1 := update(next0, midNode0 -> nearNode0)
			nearNode = midNode;				// nearNode1 := midNode0
			midNode = farNode;				// midNode1 := farNode0
			farNode = farNode.next;			// farNode1 := farNode0.next1
		}
											// next2 := phi(guard0, next1, next0)
											// nearNode2 := phi(guard0, nearNode1, nearNode0)
											// midNode2 := phi(guard0, midNode1, midNode0)
											// farNode2 := phi(guard0, farNode1, farNode0)
		assert farNode ==  null; 			// assume farNode2 = null
		
		midNode.next = nearNode;			// next3 = update(next2, midNode2 -> nearNode2)
		this.head = midNode;				// head0 = update(head, this -> midNode2)
	}

	public String toString() {
		final StringBuilder b = new StringBuilder();
		final Set<Node> nodes = new HashSet<Node>();
		b.append("[");
		if (head != null) {
			b.append(head.data);
			Node current = head.next;
			nodes.add(head);
			while(current != null && nodes.add(current)) {
				b.append(", ");
				b.append(current.data);
				current = current.next;	    		
			}
			if (current != null)
				b.append(", " + current.data + ", ...");
		}
		b.append("]");   	
		return b.toString();
	}

	public static void test(String[] in) {
		List l0 = new List();
		for(String v : in)
			l0.add(v);
		System.out.println("\nl0: " + l0);
		l0.reverse();
		System.out.println("l0.reverse(): " + l0);
		
		List l1 = new List();
		for(String v : in)
			l1.add(v);
		System.out.println("l1: " + l1);
		l1.reverseFinitized();
		System.out.println("l1.reverseFinitized(): " + l1);
	}
	
	public static void main(String[] args) {
		
		final String[] in2 = { "a", "b" }, in3 = { "a", "b", "c" };
		test(in2);
		test(in3);
	}
}

