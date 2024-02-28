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

import java.util.Collection;
import java.util.List;

import kodkod.engine.CapacityExceededException;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;


/**
 * A factory class that facilitates creation of tuples
 * and tuple sets drawn from a given universe.  Only one
 * factory per universe exists.
 * 
 * @specfield universe: Universe
 * @invariant no f: TupleFactory - this | f.universe = this.universe 
 * @author Emina Torlak
 */
public final class TupleFactory {

	private final Universe universe;
	private final int base;
	
	/**
	 * Constructs a factory for the given universe.
	 * @requires no (TupleFactory<:universe).universe
	 * @ensures this.universe' = universe
	 * @throws NullPointerException  universe = null
	 */
	TupleFactory(Universe universe) {
		this.universe = universe;
		this.base = universe.size();
	}
	
	/**
	 * Returns the universe to which this factory belongs.
	 * @return this.universe
	 */
	public Universe universe() { return universe; }
	
	/**  
     * Returns a tuple that contains the specified sequence of atoms, 
     * drawn from this.universe.
     * 
     * @return {t: Tuple | t.universe = this.universe && t.atoms = atoms }
     * @throws NullPointerException  atoms = null 
     * @throws IllegalArgumentException  atoms.length < 1
     * @throws IllegalArgumentException   some a: atoms[int] | a !in this.universe.atoms[int]
     */
	public Tuple tuple(Object... atoms) {
		if (atoms.length<1) throw new IllegalArgumentException("atoms.length<1");
		return new IntTuple(atoms);
	}
	
	/**  
     * Returns a tuple that contains the specified sequence of atoms, 
     * drawn from this.universe.
     * 
     * @return {t: Tuple | t.universe = this.universe && t.atoms = atoms }
     * @throws NullPointerException  atoms = null 
     * @throws IllegalArgumentException  atoms.size < 1
     * @throws IllegalArgumentException   some a: atoms[int] | a !in this.universe.atoms[int]
     */
	public Tuple tuple(List<?> atoms) {
		if (atoms.size()<1) throw new IllegalArgumentException("atoms.size()<1");
		return new IntTuple(atoms.toArray());
	}
	
	/**  
     * Returns a tuple with the specified arity whose index in an arity-dimensional 
     * space over this.universe is given by the index parameter.
     * 
     * @return {t: Tuple | t.universe = this.universe && t.arity = arity && 
     *                     index = sum({i : [0..arity) | universe.index(t.atoms[i]) * universe.size^(arity - 1 - i))}) }
     * @throws IllegalArgumentException  arity < 1 || index < 0 || index >= universe.size^arity
     */
	public Tuple tuple(final int arity, final int index) {
		return new IntTuple(arity, index);
	}
	
	/**
	 * Returns a set of all tuples of the given arity, drawn from this.universe.
	 * @return { s: TupleSet | s.universe = this.universe && s.arity = arity && 
	 *                         s.tuples = {t: Tuple | t.universe = this.universe && t.arity = arity} }
	 * @throws IllegalArgumentException  arity < 1                     
	 */
	public TupleSet allOf(int arity) {
		return new TupleSet(universe, arity, 
				                      0, ((int) Math.pow(base, arity)) - 1);
	}
	
	/**
	 * Returns a set of tuples of arity 1, each of which wraps one of the given objects. 
	 * The method requires that the specified object be atoms in this.universe.
	 *
	 * @return {s: TupleSet | s.universe = this.universe && s.arity = 1 &&
	 *                        s.tuples = { t: Tuple | t.universe=this.universe && 
	 *                                                t.arity=1 && t.atoms[0] in atoms[int]}}
	 * @throws NullPointerException  atoms = null
	 * @throws IllegalArgumentException  some atoms[int] - this.universe.atoms[int]
	 */
	public TupleSet setOf(Object... atoms) {
		final TupleSet ret = new TupleSet(universe, 1);
		for (Object atom: atoms) {
			ret.add(new IntTuple(atom));
		}
		return ret;
	}
	
	/**
	 * Returns a tuple set consisting of specified tuples.  The method requires that
	 * all given tuples have the same arity and be drawn from this.universe.
	 *
	 * @return {s: TupleSet | s.universe = this.universe && s.arity = first.arity &&
	 *                        s.tuples = first + rest[int] }
	 * @throws NullPointerException  first = null || rest = null
	 * @throws IllegalArgumentException  first.universe != this.universe 
	 * @throws IllegalArgumentException  some t: rest[int] | t.universe != this.universe || t.arity != first.arity
	 */
	public TupleSet setOf(Tuple first, Tuple... rest) {
		if (!first.universe().equals(universe))
			throw new IllegalArgumentException("first.universe != this.universe");

		final TupleSet ret = new TupleSet(universe, first.arity(), first.index(), first.index());
		for(Tuple tuple: rest) {
			ret.add(tuple);
		}
		return ret;
	}
	
	/**
	 * Returns a tuple set consisting of specified tuples.  The method requires that
	 * all given tuples have the same arity and be drawn from this.universe.
	 *
	 * @return {s: TupleSet | s.universe = this.universe && s.arity = first.arity &&
	 *                        s.tuples = tuples }
	 * @throws NullPointerException  tuples = null 
	 * @throws IllegalArgumentException  tuples.isEmpty()  
	 * @throws IllegalArgumentException  tuples.universe != this.universe || #tuples.arity > 1
	 */
	public TupleSet setOf(Collection<Tuple> tuples) {
		if (tuples.isEmpty())
			throw new IllegalArgumentException("tuples.isEmpty()");
		final TupleSet ret = new TupleSet(universe, tuples.iterator().next().arity());
		for(Tuple t : tuples) {
			ret.add(t);
		}
		return ret;
	}
	
	/**
	 * Returns a set of the given arity that contains all tuples whose indeces
	 * are contained in the given int set.  Throws an IllegalArgumentException
	 * if the set contains an index that is either negative or greater than
	 * this.universe.size()^arity - 1.  The returned TupleSet is backed by a clone
	 * of tupleIndices.  
	 * @requires tupleIndices is cloneable
	 * @return {s: TupleSet | s.universe = this.universe && s.arity = arity &&
	 *                        s.tuples = {t: Tuple | t.index() in tupleIndices} }
	 * @throws NullPointerException  tupleIndices = null
	 * @throws IllegalArgumentException  tupleIndices is uncloneable
	 * @throws IllegalArgumentException  arity < 1
	 * @throws IllegalArgumentException  tupleIndices.min() < 0 || tupleIndices.max() >= this.universe.size()^arity 
	 */
	public TupleSet setOf(int arity, IntSet tupleIndices) {
		try {
			return new TupleSet(universe,arity,tupleIndices.clone());
		} catch (CloneNotSupportedException cne){
			throw new IllegalArgumentException("uncloneable int set");
		}
	}
	
	/**
	 * Returns an initially empty tuple set of the given arity, based on this.universe.
	 * @return { s: TupleSet | s.universe = this.universe && s.arity = arity && no s.tuples }
	 * @throws IllegalArgumentException  arity < 1    
	 */
	public TupleSet noneOf(int arity) {
		return new TupleSet(universe, arity);
	}
	
	/**
	 * Returns a tuple set that contains all tuples between <code>from</code>
	 * and <code>to</code>, inclusive.  More formally, the returned set contains
	 * all tuples whose indices are in the range [from.index()..to.index()].
	 * @return { s: TupleSet | s.universe = this.universe && s.arity = from.arity &&
	 *                         s.tuples = {t: Tuple | t.universe = this.universe &&
	 *                                                t.arity = s.arity &&
	 *                                                from.index()<=t.index()<=to.index() }}
	 * @throws NullPointerException  from = null || to = null
	 * @throws IllegalArgumentException  from.arity != to.arity 
	 * @throws IllegalArgumentException  from.universe != this.universe || to.universe != this.universe
	 * @throws IllegalArgumentException  from.index > to.index
	 */
	public TupleSet range(Tuple from, Tuple to) {
		if (from.arity()!=to.arity()) 
			throw new IllegalArgumentException("from.arity!=to.arity");
		if (!(from.universe().equals(universe)&&to.universe().equals(universe)))
			throw new IllegalArgumentException("from.universe != this.universe || to.universe != this.universe");
		return new TupleSet(universe, from.arity(), from.index(), to.index());
	}
	
	/**
	 * Returns a tuple set that contains all tuples in the specified area
	 * of the n-dimensional space, where n is the arity of the argument
	 * tuples.  For example, suppose that this.universe consists of atoms
	 * {atom0, atom1, atom2, atom3}, where atom0 has index 0, atom1 has index 1, etc.  
	 * Calling this method with tuples [atom0, atom2] and [atom1, atom3] as the 
	 * first and second arguments would result in the set {[atom0, atom2],
	 * [atom0,atom3], [atom1,atom2], [atom1, atom3]}.  That is, the returned set
	 * consists of all points in the rectangle whose upper left corner is the 
	 * point [atom0, atom2] and whose lower right corner is at [atom1, atom3].
	 * @return {s: TupleSet | s.arity = upperLeft.arity &&
	 *                        s.universe = this.universe &&
	 *                        s.tuples = {t: Tuple | all i: [0..s.arity) | 
	 *                                     this.universe.index(upperLeft.atoms[i]) <=
	 *                                     this.universe.index(t.atoms[i]) <= 
	 *                                     this.universe.index(lowerRight.atoms[i]}}
	 * @throws NullPointerException  upperLeft = null || lowerRight = null
	 * @throws IllegalArgumentException  upperLeft.arity != lowerRight.arity 
	 * @throws IllegalArgumentException  lowerRight.universe != this.universe || upperLeft.universe != this.universe
	 * @throws IllegalArgumentException  some i: [0..upperLeft.arity) | 
	 *                                       this.universe.index(upperLeft.atoms[i]) > 
	 *                                       this.universe.index(lowerRight.atoms[i])
	 */
	public TupleSet area(Tuple upperLeft, Tuple lowerRight) {
		if (!upperLeft.universe().equals(universe) || upperLeft.arity()!=lowerRight.arity()) 
			throw new IllegalArgumentException();
		TupleSet ret = new TupleSet(universe, 1, upperLeft.atomIndex(0),lowerRight.atomIndex(0));
		for(int i = 1; i < upperLeft.arity(); i++) {
			ret = ret.product(new TupleSet(universe, 1, upperLeft.atomIndex(i),lowerRight.atomIndex(i)));
		}
		return ret;
	}
	
	/**
	 * Throws a CapacityExceededException if all tuples of the given arity 
	 * drawn from this.universe cannot be represented as an integer.
	 * @throws CapacityExceededException if all tuples of the given arity 
	 * drawn from this.universe cannot be represented as an integer.
	 */
	void checkCapacity(int arity) { 
		if (StrictMath.pow(base,arity) > Integer.MAX_VALUE) {
			throw new CapacityExceededException("Arity too large (" + arity + ") for a universe of size " + universe.size(), Ints.nCopies(arity, base));
		}
	}
	
	/**
	 * Projects the tuple with the specified index and arity onto the 
	 * specified column.    
	 * @requires tupleIndex >= 0 && tupleIndex < this.universe.size() ^ arity
	 * @return this.universe.index(this.tuple(arity, tupleIndex).atoms[i])
	 */
	int project(int tupleIndex, int arity, int column) {
		if (column < 0 || column >= arity) throw new IndexOutOfBoundsException(column+"");
        return (tupleIndex / ((int) Math.pow(base, arity-1-column))) % base;
	}
	
	/**
	 * An implementation of the Tuple interface that stores
	 * only the tuple's arity and index, rather than the full
	 * sequence of atoms.  Parts of the sequence are computed on
	 * demand, e.g. when the <code>get</code> method is invoked.
	 * 
	 * @specfield universe: TupleFactory.this.universe
	 * @specfield arity: int
	 * @specfield index: int
	 * @invariant arity >= 1 && 0 <= index < TupleFactory.this.base^arity
	 * @invariant index = sum({i: [0..arity) | TupleFactory.this.universe.index(atoms[i]) * TupleFactory.this.base^(arity - 1 - i))
	 * @author Emina Torlak
	 */
	private final class IntTuple extends Tuple {
		private final int arity, index;
		
		/**  
	     * Constructs a tuple with the specified arity and index, whose atoms
	     * are drawn from the factory's universe.
	     * 
	     * @ensures this.arity' = arity && 
	     *          this.index' = index 
	     * @throws IllegalArgumentException  arity < 1 || index < 0 || index >= TupleFactory.this.base^arity
	     */
	    IntTuple(final int arity, final int index) {
	    	checkCapacity(arity);
	        if (arity < 1 || index < 0 || index >= Math.pow(base, arity)) {
	            throw new IllegalArgumentException("arity < 1 || index < 0 || index >= universe.size^arity");
	        }
	        this.arity = arity;
	        this.index = index;
	    }
	    
	    /**  
	     * Constructs a tuple that contains the specified sequence of atoms, drawn from the
	     * enclosing factory's universe.
	     * 
	     * @requires atoms.length > 0
	     * @ensures this.atoms' = atoms
	     * @throws NullPointerException  atoms = null
	     * @throws IllegalArgumentException   some a: atoms[int] | a !in universe.atoms[int]
	     */
	    IntTuple(final Object... atoms) {
	        this.arity = atoms.length;
	        checkCapacity(arity);
	        int tempIndex = 0, multiplier = 1;
	        for (int i = arity - 1; i >= 0; i--) { 
	            tempIndex += universe.index(atoms[i]) * multiplier;
	            multiplier *= base;
	        }
	        this.index = tempIndex;
	        assert this.index >= 0;
	    }
	    
	    /**
		 * Constructs a tuple with the specified arity, with the specified atom
		 * at each position.  
		 * @ensures this.arity' = arity && this.atoms = [0..arity)->atom 
		 * @throws NullPointerException  atom = null
	     * @throws IllegalArgumentException  arity < 1 || atom !in this.universe.atoms[int]
	     */
	    @SuppressWarnings("unused")
		IntTuple(final int arity, final Object atom) {
	    	checkCapacity(arity);
	    	if (arity < 1) throw new IllegalArgumentException("arity < 1");
	    	this.arity = arity;
	    	int tempIndex = 1;
			for (int i = 0; i < arity; i++) {
				tempIndex = tempIndex*base + 1;
			}
			this.index = universe.index(atom) * tempIndex;
	        assert this.index >= 0;
	    }
	    
	    /** {@inheritDoc} */
	    public Universe universe() { return universe; }
	    
	    /** {@inheritDoc} */
	    public int arity() { return arity; }
	    
	    /** {@inheritDoc} */
	    public int index() { return index; }
	    
	    /** {@inheritDoc} */
	    public Object atom(int i) {
	        return universe.atom(atomIndex(i));
	    }
	    
	    /** {@inheritDoc} */
	   public int atomIndex(int i) {
		   return project(index,arity,i);
//	        if (i < 0 || i >= arity) throw new IndexOutOfBoundsException("i < 0 || i >= this.arity");
//	        return (index / ((int) Math.pow(base, arity-1-i))) % base;
	    }
	    
	    /** {@inheritDoc} */
	    public boolean contains(Object atom) {
	        for (int remainder = index, atomIndex = universe.index(atom); 
	                 remainder > 0; remainder = remainder / base) {
	            if (remainder % base == atomIndex) return true;
	        }
	        return false;
	    }

	    /** {@inheritDoc} */
	    public Tuple product(Tuple tuple) {
	    	if (!universe.equals(tuple.universe())) throw new IllegalArgumentException("tuple.universe != this.universe");
	        return new IntTuple(arity + tuple.arity(), 
	        		                index * ((int)Math.pow(base, tuple.arity())) + tuple.index());
	    }
	}
	
	
}
