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


/** 
 * Represents a sequence of atoms drawn from a given {@link kodkod.instance.Universe universe}.  
 * Note that a Tuple of arity n whose atoms belong to a Universe u encodes an n-digit number in
 * base u.size.  The decimal representation of this number is taken to be the index of the tuple
 * in an n-dimensional space over the Universe u.  
 * 
 * @specfield arity: int
 * @specfield universe: Universe
 * @specfield atoms: [0..arity)->one Object
 * @invariant atoms[int] in universe.atoms[int]
 *
 * @author Emina Torlak                     
 */
public abstract class Tuple  {
	
    /**
     * Returns the universe from which the atoms in this
     * tuple are drawn.
     * @return this.universe
     */
    public abstract Universe universe();
    
    /**
     * Returns the arity of this tuple.
     * @return this.arity
     */
    public abstract int arity();
    
    /**
     * A Tuple encodes a number with this.arity digits in radix this.universe.size;  
     * a Tuple's index is the decimal representation of this number.  
     *  
     * @return sum({i: [0..arity) | universe.index(atoms[i]) * universe.size^(arity - 1 - i)})
     */
    public abstract int index();
    
    /**
     * Returns the atom at the specified index
     *
     * @return this.atoms[i]
     * @throws IndexOutOfBoundsException  i < 0 || i >= this.arity
     */
    public abstract Object atom(int i);
    
    /**
     * Returns the index of the ith atom as given by this.universe.
     * The effect of this method is the same as calling this.universe.index(this.atom(i)).
     * 
     * @return this.universe.index(this.atoms[i])
     * @throws IndexOutOfBoundsException  i < 0 || i >= this.arity
     */
    public abstract int atomIndex(int i);
    
    /**
     * Returns true if atom is in this tuple, otherwise returns false.
     *
     * @return atom in this.atoms[int]
     * @throws IllegalArgumentException  atom !in this.universe.atoms[int]
     */
    public abstract boolean contains(Object atom);
    
    /**
     * Returns the cross product of this and the specified tuple.
     *
     * @return {t : Tuple | t.atoms = this.atoms->tuple.atoms}
     * @throws NullPointerException  tuple = null
     * @throws IllegalArgumentException  tuple.universe != this.universe
     */
    public abstract Tuple product(Tuple tuple);
    
    /**
     * Returns true if o is a tuple with the same sequence of atoms as this,
     * drawn from the same universe as this.  Otherwise returns false.
     * 
     * @return o in Tuple && o.universe = this.universe && o.atoms = this.atoms
     */
    public boolean equals(Object o) {
    		if (this==o) return true;
    		else if (o instanceof Tuple) {
            final Tuple t = (Tuple) o;
            return universe().equals(t.universe()) && arity()==t.arity() && index()==t.index();
        }
        else return false;   
    }
    
    /**
     * Returns a hash code based on the tuple's arity, index, and the hash code
     * of its universe, so that the general contract of Object.hashCode is obeyed.
     * @return the hashcode for this tuple
     */
    public int hashCode() {
        return (arity() * 19 + index())^universe().hashCode();
    }
    
    /**
     * @see java.lang.Object#toString()
     */
    public String toString() {
        final StringBuilder ret = new StringBuilder("[");
        ret.append(atom(0));
        for (int i = 1; i < arity(); i++) {
            ret.append(", ");
            ret.append(atom(i));
        }
        ret.append("]");
        return ret.toString();
  
    }
}
