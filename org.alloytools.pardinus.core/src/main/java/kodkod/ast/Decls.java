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
package kodkod.ast;

import java.util.Arrays;
import java.util.Iterator;

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;


/** 
 * A sequence of decls. 
 * 
 * @specfield size: int
 * @specfield decls: [0..size) -> one Decl
 * @invariant size > 0
 * @invariant children = decls
 * @author Emina Torlak 
 */
public class Decls extends Node implements Iterable<Decl> {
	private final Decl[] decls;
	
	/**
	 * Constructs a Decls object with itself as its sole
	 * declaration.  This constructor can only be called
	 * from inside the Decl constructor; otherwise it will
	 * throw a ClassCastException.
	 * @ensures this.declarations' = 0->this
	 * @throws ClassCastException  this !in Decl
	 */
    Decls() {
    	this.decls = new Decl[]{ (Decl) this };
    }
    
    /**
	 * Constructs a new Decls with the specified head and tail.
	 * @requires head.size > 0 && tail.size > 0
	 * @ensures this.size' = head.size + tail.size &&
	 *          (all i: [0..head.size) | this.decls[i] = head.decls[i]) &&
	 *          (all i: [head.size..this.size') | this.decls[i] = tail.decls[i])
	 * @throws NullPointerException  head = null || tail is null 
	 */
	private Decls(Decls head, Decls tail) {
		this.decls = new Decl[head.size()+tail.size()];
		System.arraycopy(head.decls, 0, decls, 0, head.size());
		System.arraycopy(tail.decls, 0, decls, head.size(), tail.size());
	}
    
    /**
     * Returns the number of decls in this Decls object.
     * @return this.size
     */
    public int size() { return decls.length; }
    
    /**
     * Returns the ith declaration in this Decls sequence.
     * @requires 0 <= i < this.size
     * @return this.decls[i]
     */
    public Decl get(int i) { return decls[i]; }
    
    /**
     * Returns an unmodifiable iterator over the decls in this Decls object.
     * @return an unmodifiable iterator over the decls in this Decls object.
     */
    public Iterator<Decl> iterator() { return Containers.iterate(decls); }
    
    /**
     * Returns a sequence of this.size + other.size decls that has 
     * these decls as the prefix and the given decls as the suffix.
     * @return {ds: Decls | ds.size = this.size + other.size && 
     *                      ds.decls = this.decls + 
     *                      {i: [this.size..this.size+other.size), d: Decl | d = other.decls[i-this.size] }
     * @throws NullPointerException  decl = null
     */
    public final Decls and(Decls other) {
    	return new Decls(this, other);
    }
    
    /**
     * {@inheritDoc}
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    public <E, F, D, I> D accept(ReturnVisitor<E, F, D, I> visitor) {
        return visitor.visit(this);
    }
   
    /**
     * {@inheritDoc}
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }
    
    /**
     * {@inheritDoc}
     * @see kodkod.ast.Node#toString()
     */
    public String toString() {
        return Arrays.toString(decls);
    }
    
}
