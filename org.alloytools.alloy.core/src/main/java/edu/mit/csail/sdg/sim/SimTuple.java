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

package edu.mit.csail.sdg.sim;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * Immutable; represents a tuple.
 * <p>
 * <b>Thread Safety:</b> Safe.
 */

public final class SimTuple implements Iterable<SimAtom> {

    /** Stores the tuple. */
    private SimAtom[] array;

    /** If nonzero, it caches the hash code. */
    private int       hashCode = 0;

    /**
     * Construct a tuple backed by the given array as-is; thus the caller must not
     * modify it any more.
     */
    private SimTuple(SimAtom[] array) {
        if (array.length == 0)
            throw new IllegalArgumentException();
        this.array = array;
    }

    /**
     * Construct the n-ary tuple; throws an exception if the given list is empty.
     */
    public static SimTuple make(List<SimAtom> list) {
        if (list.size() == 0)
            throw new IllegalArgumentException();
        SimAtom[] array = new SimAtom[list.size()];
        for (int i = 0, n = list.size(); i < n; i++) {
            array[i] = list.get(i);
        }
        return new SimTuple(array);
    }

    /** Construct the binary tuple (a,b) */
    public static SimTuple make(SimAtom a, SimAtom b) {
        return new SimTuple(new SimAtom[] {
                                           a, b
        });
    }

    /** Construct the unary tuple containing the given atom. */
    public static SimTuple make(SimAtom atom) {
        return new SimTuple(new SimAtom[] {
                                           atom
        });
    }

    /** Construct the unary tuple containing the given atom. */
    public static SimTuple make(String atom) {
        return new SimTuple(new SimAtom[] {
                                           SimAtom.make(atom)
        });
    }

    /**
     * Construct the tuple containing the given list of atoms; the list must not be
     * empty.
     */
    public static SimTuple make(String[] atoms) {
        SimAtom[] ans = new SimAtom[atoms.length];
        for (int i = 0; i < atoms.length; i++)
            ans[i] = SimAtom.make(atoms[i]);
        return new SimTuple(ans);
    }

    /** Write this SimTuple as (".." ".." "..") */
    void write(BufferedOutputStream out) throws IOException {
        out.write('(');
        for (int n = array.length, i = 0; i < n; i++) {
            if (i > 0)
                out.write(' ');
            array[i].write(out);
        }
        out.write(')');
    }

    /**
     * Read a (".." ".." "..") tuple assuming the leading "(" has already been
     * consumed.
     */
    static SimTuple read(BufferedInputStream in) throws IOException {
        List<SimAtom> list = new ArrayList<SimAtom>();
        while (true) {
            int c = in.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c > 0 && c <= ' ')
                continue; // skip whitespace
            if (c == ')')
                break;
            if (c != '\"')
                throw new IOException("Expecting start of atom");
            list.add(SimAtom.read(in));
            c = in.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c == ')')
                break;
            if (!(c <= ' '))
                throw new IOException("Expecting \')\' or white space after an atom.");
        }
        if (list.size() == 0)
            throw new IOException("Tuple arity cannot be 0.");
        return make(list);
    }

    /** Returns the arity of this tuple. */
    public int arity() {
        return array.length;
    }

    /** Return the i-th atom from this tuple. */
    public SimAtom get(int i) {
        return array[i];
    }

    /**
     * Returns true if this tuple contains at least one occurrence of the given
     * atom.
     */
    public boolean has(SimAtom atom) {
        for (int i = array.length - 1; i >= 0; i--)
            if (array[i] == atom)
                return true;
        return false;
    }

    /**
     * Replace the i-th atom, and return the resulting SimTuple.
     */
    public SimTuple replace(int i, SimAtom newAtom) {
        if (array[i] == newAtom)
            return this;
        SimAtom ar[] = new SimAtom[array.length];
        for (int j = 0; j < ar.length; j++)
            ar[j] = (j == i) ? newAtom : array[j];
        return new SimTuple(ar);
    }

    /**
     * Replace each atom using the given SimAtom->SimAtom map; any atom not in the
     * map will stay unchanged.
     */
    public SimTuple replace(Map<SimAtom,SimAtom> map) {
        SimAtom[] newarray = new SimAtom[array.length];
        for (int i = array.length - 1; i >= 0; i--) {
            SimAtom oldX = array[i];
            SimAtom newX = map.get(oldX);
            newarray[i] = (newX == null ? oldX : newX);
        }
        return new SimTuple(newarray);
    }

    /**
     * Prepend the given atom to the front of this tuple, then return the resulting
     * new Tuple.
     */
    public SimTuple prepend(SimAtom atom) {
        SimAtom[] newarray = new SimAtom[array.length + 1];
        newarray[0] = atom;
        for (int i = 0; i < array.length; i++)
            newarray[i + 1] = array[i];
        return new SimTuple(newarray);
    }

    /**
     * Append the given atom to the back of this tuple, then return the resulting
     * new Tuple.
     */
    public SimTuple append(SimAtom atom) {
        SimAtom[] newarray = new SimAtom[array.length + 1];
        for (int i = 0; i < array.length; i++)
            newarray[i] = array[i];
        newarray[array.length] = atom;
        return new SimTuple(newarray);
    }

    /** Return the product of this tuple and that tuple. */
    public SimTuple product(SimTuple that) {
        SimAtom[] c = new SimAtom[array.length + that.array.length]; // If
                                                                    // integer
                                                                    // overflows,
                                                                    // we'll
                                                                    // get
                                                                    // an
                                                                    // exception
                                                                    // here,
                                                                    // which
                                                                    // is
                                                                    // good
        for (int i = 0; i < this.array.length; i++)
            c[i] = array[i];
        for (int i = 0; i < that.array.length; i++)
            c[i + array.length] = that.array[i];
        return new SimTuple(c);
    }

    /**
     * Return the relational join of this tuple and that tuple; throws an exception
     * if the join point doesn't match or if both sides are unary.
     */
    public SimTuple join(SimTuple that) {
        if (array.length + that.array.length == 2 || array[array.length - 1] != that.array[0])
            throw new IllegalArgumentException();
        SimAtom[] c = new SimAtom[array.length + that.array.length - 2]; // If
                                                                        // integer
                                                                        // overflows,
                                                                        // we'll
                                                                        // get
                                                                        // an
                                                                        // exception
                                                                        // here,
                                                                        // which
                                                                        // is
                                                                        // good
        for (int i = 0; i < this.array.length - 1; i++)
            c[i] = array[i];
        for (int i = 0; i < that.array.length - 1; i++)
            c[i + array.length - 1] = that.array[i + 1];
        return new SimTuple(c);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int ans = hashCode;
        if (ans == 0) {
            // We already know each SimAtom has been canonicalized, so just
            // computing its IdentityHashCode is faster
            for (int i = array.length - 1; i >= 0; i--)
                ans = ans * 31 + System.identityHashCode(array[i]);
            if (ans == 0)
                ans++; // so that we don't end up re-computing this SimTuple's
                      // hashcode over and over again
            hashCode = ans;
        }
        return ans;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object that) {
        if (this == that)
            return true;
        else if (!(that instanceof SimTuple))
            return false;
        SimAtom[] other = ((SimTuple) that).array;
        if (array == other)
            return true;
        else if (array.length != other.length)
            return false;
        if (hashCode() != that.hashCode())
            return false;
        for (int i = array.length - 1; i >= 0; i--)
            if (array[i] != other[i])
                return false;
        array = other;
        // Change it so we share the same array; this is thread safe since these
        // array contents are never mutated,
        // so it doesn't matter if some thread sees the old array and some sees
        // the new array.
        // JLS 3rd Edition 17.7 guarantees that writes and reads of references
        // are atomic though not necessarily visible,
        // so another thread will either see the old array or the new array.
        return true;
    }

    /** Returns the first atom of this tuple. */
    public SimAtom head() {
        return array[0];
    }

    /** Returns the last atom of this tuple. */
    public SimAtom tail() {
        return array[array.length - 1];
    }

    /**
     * Returns the subtuple containing the first n atoms (n must be between 1 and
     * arity)
     */
    public SimTuple head(int n) {
        if (n <= 0 || n > array.length)
            throw new IllegalArgumentException();
        else if (n == array.length)
            return this;
        SimAtom newtuple[] = new SimAtom[n];
        for (int c = 0; c < newtuple.length; c++)
            newtuple[c] = array[c];
        return new SimTuple(newtuple);
    }

    /**
     * Returns the subtuple containing the last n atoms (n must be between 1 and
     * arity)
     */
    public SimTuple tail(int n) {
        if (n <= 0 || n > array.length)
            throw new IllegalArgumentException();
        else if (n == array.length)
            return this;
        SimAtom newtuple[] = new SimAtom[n];
        for (int a = array.length - n, c = 0; c < newtuple.length; c++)
            newtuple[c] = array[c + a];
        return new SimTuple(newtuple);
    }

    /**
     * Write a human-readable representation of this tuple into the given
     * StringBuilder object.
     */
    public void toString(StringBuilder sb) {
        for (int i = 0; i < array.length; i++) {
            if (i > 0)
                sb.append("->");
            sb.append(array[i]);
        }
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(sb);
        return sb.toString();
    }

    /** {@inheritDoc} */
    @Override
    public Iterator<SimAtom> iterator() {
        return new Iterator<SimAtom>() {

            private int i = 0; // the next index to read out

            @Override
            public boolean hasNext() {
                return i < array.length;
            }

            @Override
            public SimAtom next() {
                if (i < array.length) {
                    i++;
                    return array[i - 1];
                } else
                    throw new NoSuchElementException();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }
}
