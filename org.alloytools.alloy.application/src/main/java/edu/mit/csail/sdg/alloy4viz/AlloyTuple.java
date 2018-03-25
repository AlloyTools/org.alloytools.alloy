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

package edu.mit.csail.sdg.alloy4viz;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Util;

/**
 * Immutable; represents an Alloy tuple.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyTuple implements Comparable<AlloyTuple> {

    /** The unmodifiable list of atoms in this tuple. */
    private final ConstList<AlloyAtom> atoms;

    /**
     * Creates a new AlloyTuple containing the atoms specified by the list;
     * atoms.size() must be 2 or above.
     */
    public AlloyTuple(List<AlloyAtom> atoms) {
        if (atoms == null || atoms.size() < 2)
            throw new RuntimeException("An AlloyTuple object must have 2 or more atoms.");
        this.atoms = ConstList.make(atoms);
    }

    /**
     * Creates a new AlloyTuple containing the atoms specified by the list;
     * atoms.size() must be 2 or above.
     */
    public AlloyTuple(AlloyAtom... atoms) {
        if (atoms == null || atoms.length < 2)
            throw new RuntimeException("An AlloyTuple object must have 2 or more atoms.");
        this.atoms = Util.asList(atoms);
    }

    /**
     * Project this tuple and return an unmodifiable list of remaining atoms (after
     * removing zero or more columns)
     *
     * @param columns - the collection of columns to remove (0 is the first column,
     *            1 is the second column...)
     */
    public ConstList<AlloyAtom> project(Collection<Integer> columns) {
        TempList<AlloyAtom> list = new TempList<AlloyAtom>(atoms.size());
        for (int i = 0; i < atoms.size(); i++)
            if (!columns.contains(i))
                list.add(atoms.get(i));
        if (list.size() == atoms.size())
            return atoms;
        else
            return list.makeConst();
    }

    /** Returns the arity of this AlloyTuple. */
    public int getArity() {
        return atoms.size();
    }

    /**
     * Returns an unmodifiable list of the AlloyAtoms in this AlloyTuple.
     */
    public List<AlloyAtom> getAtoms() {
        return atoms;
    }

    /** Returns the first AlloyAtom in this AlloyTuple. */
    public AlloyAtom getStart() {
        return atoms.get(0);
    }

    /** Returns the last AlloyAtom in this AlloyTuple. */
    public AlloyAtom getEnd() {
        return atoms.get(atoms.size() - 1);
    }

    /**
     * Returns a new AlloyTuple whose list of atoms is the same but in reverse.
     */
    public AlloyTuple reverse() {
        List<AlloyAtom> newlist = new ArrayList<AlloyAtom>(atoms.size());
        for (int i = atoms.size() - 1; i >= 0; i--)
            newlist.add(atoms.get(i));
        return new AlloyTuple(newlist);
    }

    /**
     * Provides a human-readable description of this AlloyTuple.
     */
    @Override
    public String toString() {
        String s = "<";
        for (int i = 0; i < atoms.size(); i++) {
            if (i != 0)
                s = s + ", ";
            s = s + atoms.get(i);
        }
        return s + ">";
    }

    /**
     * Two tuples are first compared based on length; if the length is the same, we
     * compare atom-by-atom. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    @Override
    public int compareTo(AlloyTuple that) {
        if (that == null)
            return 1;
        if (atoms.size() < that.atoms.size())
            return -1;
        if (atoms.size() > that.atoms.size())
            return 1;
        for (int i = 0; i < atoms.size(); i++) {
            int result = atoms.get(i).compareTo(that.atoms.get(i));
            if (result != 0)
                return result;
        }
        return 0;
    }

    /**
     * Two tuples are equal if they have the same atoms in the same order.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyTuple))
            return false;
        if (other == this)
            return true;
        return atoms.equals(((AlloyTuple) other).atoms);
    }

    /** Compute a hash code based on the list of atoms. */
    @Override
    public int hashCode() {
        return atoms.hashCode();
    }
}
