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
 * A tree with integer keys.  
 * 
 * @specfield root: lone N
 * @specfield nodes: root.*(left + right)
 * @author Emina Torlak
 */
final class IntTree<N extends IntTree.Node<N>> implements Cloneable {
	private static final boolean BLACK = true, RED = false;

	private N root;

	/**
	 * Creates an empty IntTree.
	 * @ensures no this.root'
	 */
	IntTree() {
		root = null;
	}

	/**
	 * Discards all elements from this tree.
	 * @ensures  no this.root' 
	 **/
	final void clear() {
		root = null;
	}

	/**
	 * Returns the node with the given key, or null no such node exists.
	 * @return this.nodes & key.index 
	 */
	final N search(int k) {	
		N node = root;
		while(node != null) {
			if (node.key==k) break;
			else if (node.key>k) node = node.left;
			else node = node.right;
		}
		return node;
	}

	/**
	 * Returns the node whose key is the ceiling of <tt>k</tt> in this tree, or 
	 * null if no such node exists.
	 * @return {n: this.nodes | n.key >= k &&
	 *           no n': this.nodes - n | n'.key >= k && n'.key < n.key }
	 */
	final N searchGTE(int k) {
		if (root==null) return null;
		N c = root;
		while (true) {
			if (c.key==k) {
				return c;
			} else if (c.key>k) {
				if (c.left != null)
					c = c.left;
				else
					return c;
			} else {
				if (c.right != null) 
					c = c.right;
				else 
					return successor(c);
			}
		}
	}

	/**
	 * Returns the node whose key is the floor of <tt>k</tt> in this tree, or 
	 * null if no such node exists.
	 * @return {n: this.nodes | n.key <= k &&
	 *           no n': this.nodes - n | n'.key <= k && n'.key > n.key }
	 */
	final N searchLTE(int k) {
		if (root==null) return null;
		N f = root;
		while(true) {
			if (f.key==k)
				return f;
			else if (f.key>k) {
				if (f.left != null)
					f = f.left;
				else 
					return predecessor(f);
			} else {
				if (f.right != null) 
					f = f.right;
				else 
					return f;
			}
		}
	}

	/**
	 * Implementation of the tree-predecessor algorithm from CLR.
	 * Returns the given node's predecessor, if it exists.  
	 * Otherwise returns null.  
	 * @return the given node's predecessor
	 * @throws NullPointerException  node = null
	 */
	final N predecessor(N node) {
		if (node.left != null) {
			return max(node.left);
		} else {
			N n = node;
			N ancestor = n.parent;
			while (ancestor != null && n == ancestor.left) {
				n = ancestor;
				ancestor = ancestor.parent;
			}
			return ancestor;
		}
	}	

	/**
	 * Implementation of the tree-successor algorithm from CLR.
	 * Returns the given node's successor, if it exists.  
	 * Otherwise returns null.
	 * @return the given node's successor
	 * @throws NullPointerException  node = null
	 */
	final N successor(N node) {
		if (node.right != null) {
			return min(node.right);
		} else {
			N n = node;
			N ancestor = n.parent;
			while (ancestor != null && n == ancestor.right) {
				n = ancestor;
				ancestor = ancestor.parent;
			}
			return ancestor;
		}
	}

	/**
	 * Returns the node with the smallest key.
	 * @return key.(min(this.nodes.key))
	 */
	final N min() {
		return min(root);
	}

	/**
	 * Returns the node with the largest key.
	 * @return key.(max(this.nodes.key))
	 */
	final N max() {
		return max(root);
	}

	/**
	 * Returns the leftmost node in the subtree rooted at start.
	 * The behavior of this method is unspecified if the given node
	 * is not in this tree.
	 * @requires node in this.nodes
	 * @return {n: start.*left | no n.left }
	 */
	private final N min(N start) {
		if (start != null) {
			while(start.left != null) {
				start = start.left;
			}
		}
		return start;
	}

	/**
	 * Returns the rightmost in the subtree rooted at start.
	 * The behavior of this method is unspecified if the given node
	 * is not in this tree.
	 * @requires node in this.nodes
	 * @return {n: start.*left | no n.right }
	 */
	private final N max(N start) {
		if (start != null) {
			while(start.right != null) {
				start = start.right;
			}
		}
		return start;
	}

	/**
	 * Replaces the old node, o, with the given new node, n, in this tree.
	 * @requires no n.(left + right + parent)
	 * @requires o = o.parent.left => n.key < o.parent.key
	 * @requires o = o.parent.right => n.key > o.parent.key
	 * @requires some o.left => n.key > o.left.key
	 * @requires some o.right => n.key < o.right.key
	 * @ensures this.nodes' = this.nodes - o + n
	 * @ensures o.parent' = o.left' = o.right' = null
	 */
	final void replace(N o, N n) {
		n.color = o.color;
		n.parent = o.parent;
		n.left = o.left;
		n.right = o.right;
		if (o.left != null) 			{ o.left.parent = n; }
		if (o.right != null)			{ o.right.parent = n;	 }	 
		if (o.parent == null)			{ root = n; }
		else if (o == o.parent.left) 	{ o.parent.left = n; }
		else 							{ o.parent.right = n; }
		o.parent = o.left = o.right = null;
	}

	private final N parentOf(N n) 					{ return n==null ? null : n.parent; }
	private final N leftOf(N n) 					{ return n==null ? null : n.left; }
	private final N rightOf(N n) 					{ return n==null ? null : n.right; }
	private final boolean colorOf(N n) 				{ return n==null ? BLACK : n.color; }
	private final void setColor(N n, boolean color)	{ if (n!=null) n.color = color; }

	/**
	 * Implementation of the CLR insertion algorithm.
	 * @requires no z.key & this.nodes.key
	 * @ensures this.nodes' = this.nodes + z
	 */
	final void insert(N z) {
		N y = null;
		for (N x = root; x != null;) {
			y = x;
			if (x.key>z.key) 
				x = x.left; 
			else 
				x = x.right; 
		}

		z.parent = y;
		z.left = z.right = null;
		if (y==null) {	
			root = z;
		} else {
			z.color = RED;
			if (y.key>z.key)	{ y.left = z; }
			else 				{ y.right = z; }

			insertFixUp(z);
		}
	}

	/**
	 * A slightly modified implementation of the CLR deletion algorithm.
	 * @requires z in this.nodes
	 * @ensures this.nodes' = this.nodes - z
	 */
	final void delete(N z) {
		N y = (z.left==null || z.right==null ? z : successor(z));
		N x = (y.left != null ? y.left : y.right);
		
		N yparent = y.parent;
		final boolean yleft = (y==leftOf(y.parent));
		final boolean ycolor = y.color;
		
		if (x!=null)						{ x.parent = yparent; }
		
		if (yparent == null)				{ root = x; }
		else if (yleft)						{ yparent.left = x; }
		else								{ yparent.right = x; }
		
		if (y != z) { replace(z, y); }
		
		if (ycolor==BLACK) {
			if (x!=null) { 
				deleteFixUp(x); 
			} else if (yparent!=null) { 	// z is not the only node

				if (z==yparent) yparent = y; // y, z's successor, is z's right child
				z.color = BLACK;
				z.left = z.right = null;
				z.parent = yparent;
				if (yleft)				{ yparent.left = z; }
				else 					{ yparent.right = z; }
		
				deleteFixUp(z);
				if (z==z.parent.left)	{ z.parent.left = null; }
				else 					{ z.parent.right = null; }				
			}
		}
		
		z.left = z.right = z.parent = null; // cut z out of the tree by nulling out its pointers
	}

	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#clone()
	 * @throws CloneNotSupportedException  nodes contained in this tree are not cloneable
	 */
	@SuppressWarnings("unchecked")
	protected IntTree<N> clone() throws CloneNotSupportedException {
		final IntTree<N> ret = (IntTree<N>) super.clone();
		ret.root = clone(root, null);
		return ret;
	}

	/**
	 * Recursively clones the given node.
	 */
	@SuppressWarnings("unchecked")
	private N clone(N n, N parent) throws CloneNotSupportedException {
		if (n==null) return null;
		N clone = (N) n.clone();
		clone.parent = parent;
		clone.left = clone(n.left, clone);
		clone.right = clone(n.right, clone);
		return clone;
	}

	/*---------balancing operations (CLR, pp.278-289)---------*/
	/**
	 * From CLR.
	 */
	private void insertFixUp(N z) {
		while (z != null && z != root && z.parent.color == RED) {
			if (parentOf(z) == leftOf(parentOf(parentOf(z)))) {
				N y = rightOf(parentOf(parentOf(z)));
				if (colorOf(y) == RED) {
					setColor(parentOf(z), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(z)), RED);
					z = parentOf(parentOf(z));
				} else {
					if (z == rightOf(parentOf(z))) {
						z = parentOf(z);
						rotateLeft(z);
					}
					setColor(parentOf(z), BLACK);
					setColor(parentOf(parentOf(z)), RED);
					if (parentOf(parentOf(z)) != null)
						rotateRight(parentOf(parentOf(z)));
				}
			} else {
				N y = leftOf(parentOf(parentOf(z)));
				if (colorOf(y) == RED) {
					setColor(parentOf(z), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(z)), RED);
					z = parentOf(parentOf(z));
				} else {
					if (z == leftOf(parentOf(z))) {
						z = parentOf(z);
						rotateRight(z);
					}
					setColor(parentOf(z),  BLACK);
					setColor(parentOf(parentOf(z)), RED);
					if (parentOf(parentOf(z)) != null)
						rotateLeft(parentOf(parentOf(z)));
				}
			}
		}
		root.color = BLACK;
	}

	/**
	 * From CLR.
	 */
	private void deleteFixUp(N x) {
		while (x != root && colorOf(x) == BLACK) {
			if (x == leftOf(parentOf(x))) {
				N sib = rightOf(parentOf(x));

				if (colorOf(sib) == RED) {
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateLeft(parentOf(x));
					sib = rightOf(parentOf(x));
				}

				if (colorOf(leftOf(sib))  == BLACK &&
						colorOf(rightOf(sib)) == BLACK) {
					setColor(sib,  RED);
					x = parentOf(x);
				} else {
					if (colorOf(rightOf(sib)) == BLACK) {
						setColor(leftOf(sib), BLACK);
						setColor(sib, RED);
						rotateRight(sib);
						sib = rightOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(rightOf(sib), BLACK);
					rotateLeft(parentOf(x));
					x = root;
				}
			} else { // symmetric
				N sib = leftOf(parentOf(x));

				if (colorOf(sib) == RED) {
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateRight(parentOf(x));
					sib = leftOf(parentOf(x));
				}

				if (colorOf(rightOf(sib)) == BLACK &&
						colorOf(leftOf(sib)) == BLACK) {
					setColor(sib,  RED);
					x = parentOf(x);
				} else {
					if (colorOf(leftOf(sib)) == BLACK) {
						setColor(rightOf(sib), BLACK);
						setColor(sib, RED);
						rotateLeft(sib);
						sib = leftOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(leftOf(sib), BLACK);
					rotateRight(parentOf(x));
					x = root;
				}
			}
		}

		setColor(x, BLACK);

	}

	/**
	 * From CLR.
	 */
	private void rotateLeft(N x) {
		N y = x.right;
		x.right = y.left;
		if (y.left != null) 
			y.left.parent = x;
		y.parent = x.parent;
		if (x.parent == null)
			root = y;
		else if (x.parent.left == x)
			x.parent.left = y;
		else
			x.parent.right = y;
		y.left = x;
		x.parent = y;
	}

	/**
	 * From CLR.
	 */
	private void rotateRight(N x) {
		N y = x.left;
		x.left = y.right;  
		if (y.right != null) 
			y.right.parent = x;
		y.parent = x.parent;
		if (x.parent == null)
			root = y;
		else if (x.parent.right == x)
			x.parent.right = y;
		else 
			x.parent.left = y;
		y.right = x;
		x.parent = y;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return root.toString();
	}

	/**
	 * A node  in an int tree.  Subclasses need to 
	 * implement the clone method iff IntTree.clone will
	 * be called on the tree containing the nodes.
	 * @specfield key: int
	 * @specfield parent: lone N
	 * @specfield left: lone N
	 * @specfield right: lone N
	 * @author Emina Torlak
	 */
	abstract static class Node<N extends Node<N>> implements Cloneable {
		N parent, left, right;
		boolean color;
		/**
		 * Subclasses are required to maintain the following invariant:
		 * @invariant 	this = this.parent.left => this.key < this.parent.key &&
		 *  			this = this.parent.right => this.key > this.parent.key &&
		 *  			some this.left => this.key > this.left.key &&
		 *  			some this.right => this.key < this.right.key
		 */
		protected int key;

		/**
		 * Constructs an empty node with the given key.
		 * @ensures no this.(parent' + left' + right') && this.key' = key 
		 */
		Node(int key) {
			this.parent = this.left = this.right = null;
			this.color = BLACK;
			this.key = key;
		}

		/**
		 * Returns the left child of this node.
		 * @return this.left
		 */
		final N left() { return left; }

		/**
		 * Returns the right child of this node.
		 * @return this.right
		 */
		final N right() { return right; }

		/**
		 * Return the parent of this node.
		 * @return this.parent
		 */
		final N parent() { return parent; }

		/**
		 * Clones this node.  Subclasses must override
		 * this method (and call super.clone()) in order
		 * for IntTree.clone() to function properly.
		 * @throws CloneNotSupportedException 
		 * @see java.lang.Object#clone()
		 */
		@SuppressWarnings("unchecked")
		protected Node<N> clone() throws CloneNotSupportedException {
			Node<N> ret = (Node<N>) super.clone();
			ret.parent = ret.left = ret.right = null;
			return ret;
		}

		/**
		 * @see java.lang.Object#toString()
		 */
		public String toString() {
			return "[" + key + " " + (color ? "b" : "r") + " " + (left==this ? key : left) + " "+ 
			(right==this ? key : right)  + "]";

		}
	}

}
