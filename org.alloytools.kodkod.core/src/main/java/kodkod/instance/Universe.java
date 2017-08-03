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
package kodkod.instance;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import kodkod.util.collections.Containers;

/** 
 * <p>Represents an ordered set of unique atoms.  Objects used as atoms <b>must</b> properly  
 * implement {@link java.lang.Object#equals equals} and {@link java.lang.Object#hashCode hashCode}
 * methods.  The behavior of a universe is not specified if the value of an object is changed in a 
 * manner that affects equals comparisons while the object is an atom in the universe.</p>
 * 
 * <p>Each universe provides a {@link kodkod.instance.TupleFactory tuple factory}
 * to facilitate creation of {@link kodkod.instance.Tuple tuples} and 
 * {@link kodkod.instance.TupleSet sets of tuples} based on the atoms in the universe.</p>
 * 
 * <p><b>Implementation Note:</b> although the atoms in a universe are not interpreted in any
 * way by the Kodkod engine, it is strongly recommended that the atoms
 * of the same 'type' be grouped together.  For instance, suppose that a client model is specified in
 * terms of disjoint types Person = {Person0, Person1, Person2} and Dog = {Dog0, Dog1}.  Then, 
 * the client may observe an improvement in performance if he constructs the universe over the
 * sequences {Person0, Person1, Person2, Dog0, Dog1} or {Dog0, Dog1, Person0, Person1, Person2} rather
 * than any other permutation of these five atoms.
 * 
 * @specfield size: int
 * @specfield atoms: [0..size)->one Object
 * @specfield factory: TupleFactory
 * @invariant factory = (TupleFactory<:universe).this
 * @invariant size > 0
 * @author Emina Torlak 
 */
public final class Universe implements Iterable<Object> {
	private final Object[] atoms;
	private final Map<Object,Integer> indices;
	private final TupleFactory factory;
	
	/**  
	 * Constructs a new Universe consisting of the given atoms, in the order that they are returned 
	 * by the specified Collection's Iterator.
	 * 
	 * @ensures this.size' = atoms.size && this.atoms' = atoms.iterator
	 * @throws NullPointerException  atoms = null 
	 * @throws IllegalArgumentException  atoms contains duplicates
	 * @throws IllegalArgumentException  atoms is empty
	 */
	public Universe(Collection<?> atoms) {
		if (atoms.isEmpty()) throw new IllegalArgumentException("Cannot create an empty universe.");
		this.atoms = new Object[atoms.size()];
		this.indices = new HashMap<Object, Integer>();
		int i = 0;
		for (Object atom : atoms) {
			if (indices.containsKey(atom))
				throw new IllegalArgumentException(atom + " appears multiple times."); 
			indices.put(atom, i); 
			this.atoms[i] = atom;
			i++;
		}
		this.factory = new TupleFactory(this);
	}
	
	/**  
	 * Constructs a new Universe consisting of the given atoms, in the order that they appear 
	 * in the specified array
	 * 
	 * @ensures this.size' = atoms.length && this.atoms' = atoms
	 * @throws NullPointerException  atoms = null 
	 * @throws IllegalArgumentException  atoms contains duplicates
	 * @throws IllegalArgumentException  atoms is empty
	 */
	public Universe(Object...atoms) { 
		if (atoms.length==0) throw new IllegalArgumentException("Cannot create an empty universe.");
		this.atoms = Containers.copy(atoms, new Object[atoms.length]);
		this.indices = new HashMap<Object, Integer>();
		for (int i = 0; i < atoms.length; i++) {
			if (indices.containsKey(atoms[i]))
				throw new IllegalArgumentException(atoms[i] + " appears multiple times."); 
			indices.put(atoms[i], i);	              	
		}
		this.factory = new TupleFactory(this);
	}
	
	/**
//	 * Returns a universe that stores the given atoms explicitly, in the specified order.
//	 * The returned universe provides constant time index and atom lookup.
//	 * @ensures { u: Universe | u.size = atoms.length && u.atoms = atoms }
//	 * @throws IllegalArgumentException  atoms contains duplicates
//	 * @throws IllegalArgumentException  atoms is empty  
//	 */
//	public static Universe universe(Object...atoms) { return new ExplicitUniverse(atoms); }
//	
//	/**
//	 * Returns a universe that stores the given atoms explicitly, in the order in which they 
//	 * are returned by the collection's iterator.  The returned universe provides constant 
//	 * time index and atom lookup.
//	 * @ensures { u: Universe | u.size = atoms.size() && u.atoms[int] = atoms }
//	 * @throws IllegalArgumentException  atoms contains duplicates
//	 * @throws IllegalArgumentException  atoms is empty  
//	 */
//	public static Universe universe(Collection<?> atoms) { return new ExplicitUniverse(atoms); }
	
	/**
	 * Returns a TupleFactory that can be used to construct tuples and sets
	 * of tuples based on this universe.
	 * @return this.factory
	 */
	public TupleFactory factory() { return this.factory; }
	
	/**
	 * Returns the size of this universe
	 *
	 * @return #this.atoms
	 */
	public int size() { return atoms.length; }
	
	/**
	 * Returns true if atom is in this universe, otherwise returns false.
	 *
	 * @return atom in this.atoms[int]
	 */
	public boolean contains(Object atom) { return indices.containsKey(atom); }
	
	/**
	 * Returns the i_th atom in this universe
	 * 
	 * @return this.atoms[i]
	 * @throws IndexOutOfBoundsException  i < 0 || i >= this.size
	 */
	public Object atom(int index) { 
		if (index<0||index>=atoms.length) 
			throw new IndexOutOfBoundsException("Invalid universe index: " + index);
		return atoms[index];
	}
	
	/**
	 * Returns the index of the specified atom in this universe; if the
	 * atom is not in this universe, an IllegalArgumentException is thrown.
	 * 
	 * @return this.atoms.atom
	 * @throws IllegalArgumentException  no this.atoms.atom
	 */
	public int index(Object atom) { 
		if (indices.containsKey(atom)) return indices.get(atom);
		else throw new IllegalArgumentException("No such atom in the universe: " + atom);
	}
	
	/**
	 * Returns an iterator over atoms in this universe, according to their
	 * order in the universe.
	 * @return an iterator over atoms in this universe, according to their
	 * order in the universe
	 */
	public Iterator<Object> iterator() {
		return Containers.iterate(atoms);
	}
	
	/**
	 * Returns a string representation of this universe.
	 * @return string representation of this universe.
	 */
	public String toString() { 
		return Arrays.toString(atoms);
	}
	
}
