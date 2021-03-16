/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.NoSuchElementException;

import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/*
 * Created on 9 oct. 2003
 */

/**
 * A vector specific for primitive integers, widely used in the solver. Note
 * that if the vector has a sort method, the operations on the vector DO NOT
 * preserve sorting.
 * 
 * @author leberre
 */
public final class VecInt implements IVecInt {
    // MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson
    //
    // Permission is hereby granted, free of charge, to any person obtaining a
    // copy of this software and associated documentation files (the
    // "Software"), to deal in the Software without restriction, including
    // without limitation the rights to use, copy, modify, merge, publish,
    // distribute, sublicense, and/or sell copies of the Software, and to
    // permit persons to whom the Software is furnished to do so, subject to
    // the following conditions:
    //
    // The above copyright notice and this permission notice shall be included
    // in all copies or substantial portions of the Software.
    //
    // THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
    // OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    // MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    // NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
    // LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
    // OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
    // WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

    private static final long serialVersionUID = 1L;

    public static final IVecInt EMPTY = new EmptyVecInt();

    public VecInt() {
        this(5);
    }

    public VecInt(int size) {
        this.myarray = new int[size];
    }

    /**
     * Adapter method to translate an array of int into an IVecInt.
     * 
     * The array is used inside the VecInt, so the elements may be modified
     * outside the VecInt. But it should not take much memory.The size of the
     * created VecInt is the length of the array.
     * 
     * @param lits
     *            a filled array of int.
     */
    public VecInt(int[] lits) { // NOPMD
        this.myarray = lits;
        this.nbelem = lits.length;
    }

    /**
     * Build a vector of a given initial size filled with an integer.
     * 
     * @param size
     *            the initial size of the vector
     * @param pad
     *            the integer to fill the vector with
     */
    public VecInt(int size, int pad) {
        this.myarray = new int[size];
        for (int i = 0; i < size; i++) {
            this.myarray[i] = pad;
        }
        this.nbelem = size;
    }

    public int size() {
        return this.nbelem;
    }

    /**
     * Remove the latest nofelems elements from the vector
     * 
     * @param nofelems
     *            the number of elements to remove
     */
    public void shrink(int nofelems) {
        // assert nofelems >= 0;
        // assert nofelems <= size();
        this.nbelem -= nofelems;
    }

    public void shrinkTo(int newsize) {
        // assert newsize >= 0;
        // assert newsize < nbelem;
        this.nbelem = newsize;
    }

    /**
     * depile le dernier element du vecteur. Si le vecteur est vide, ne fait
     * rien.
     */
    public IVecInt pop() {
        // assert size() != 0;
        --this.nbelem;
        return this;
    }

    public void growTo(int newsize, final int pad) {
        // assert newsize > size();
        ensure(newsize);
        while (--newsize >= 0) {
            this.myarray[this.nbelem++] = pad;
        }
    }

    public void ensure(int nsize) {
        if (nsize >= this.myarray.length) {
            int[] narray = new int[Math.max(nsize, this.nbelem * 2)];
            System.arraycopy(this.myarray, 0, narray, 0, this.nbelem);
            this.myarray = narray;
        }
    }

    public IVecInt push(int elem) {
        ensure(this.nbelem + 1);
        this.myarray[this.nbelem++] = elem;
        return this;
    }

    public void unsafePush(int elem) {
        this.myarray[this.nbelem++] = elem;
    }

    public void clear() {
        this.nbelem = 0;
    }

    public int last() {
        // assert nbelem > 0;
        return this.myarray[this.nbelem - 1];
    }

    public int get(int i) {
        // assert i >= 0 && i < nbelem;
        return this.myarray[i];
    }

    public int unsafeGet(int i) {
        return this.myarray[i];
    }

    public void set(int i, int o) {
        assert i >= 0 && i < this.nbelem;
        this.myarray[i] = o;
    }

    public boolean contains(int e) {
        final int[] workArray = this.myarray; // dvh, faster access
        for (int i = 0; i < this.nbelem; i++) {
            if (workArray[i] == e) {
                return true;
            }
        }
        return false;
    }

    /**
     * @since 2.2
     */
    public int indexOf(int e) {
        final int[] workArray = this.myarray; // dvh, faster access
        for (int i = 0; i < this.nbelem; i++) {
            if (workArray[i] == e) {
                return i;
            }
        }
        return -1;
    }

    public int containsAt(int e) {
        return containsAt(e, -1);
    }

    public int containsAt(int e, int from) {
        final int[] workArray = this.myarray; // dvh, faster access
        for (int i = from + 1; i < this.nbelem; i++) {
            if (workArray[i] == e) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Copy the content of this vector into another one. Uses Java
     * {@link System#arraycopy(Object, int, Object, int, int)} to make the copy.
     * 
     * @param copy
     *            another VecInt vector
     */
    public void copyTo(IVecInt copy) {
        VecInt ncopy = (VecInt) copy;
        int nsize = this.nbelem + ncopy.nbelem;
        ncopy.ensure(nsize);
        System.arraycopy(this.myarray, 0, ncopy.myarray, ncopy.nbelem,
                this.nbelem);
        ncopy.nbelem = nsize;
    }

    /**
     * Copy the content of this vector into an array of integer. Uses Java
     * {@link System#arraycopy(Object, int, Object, int, int)} to make the copy.
     * 
     * @param is
     *            the target array.
     */
    public void copyTo(int[] is) {
        // assert is.length >= nbelem;
        System.arraycopy(this.myarray, 0, is, 0, this.nbelem);
    }

    public void moveTo(IVecInt dest) {
        copyTo(dest);
        this.nbelem = 0;
    }

    public void moveTo2(IVecInt dest) {
        VecInt ndest = (VecInt) dest;
        int tmp[] = ndest.myarray;
        ndest.myarray = this.myarray;
        ndest.nbelem = this.nbelem;
        this.myarray = tmp;
        this.nbelem = 0;
    }

    public void moveTo(int dest, int source) {
        this.myarray[dest] = this.myarray[source];
    }

    public void moveTo(int[] dest) {
        System.arraycopy(this.myarray, 0, dest, 0, this.nbelem);
        this.nbelem = 0;
    }

    public void moveTo(int sourceStartingIndex, int[] dest) {
        System.arraycopy(this.myarray, sourceStartingIndex, dest, 0,
                this.nbelem - sourceStartingIndex);
        this.nbelem = 0;
    }

    /**
     * Insert an element at the very beginning of the vector. The former first
     * element is appended to the end of the vector in order to have a constant
     * time operation.
     * 
     * @param elem
     *            the element to put first in the vector.
     */
    public void insertFirst(final int elem) {
        if (this.nbelem > 0) {
            push(this.myarray[0]);
            this.myarray[0] = elem;
            return;
        }
        push(elem);
    }

    /**
     * Remove an element that belongs to the Vector. The method will break if
     * the element does not belong to the vector.
     * 
     * @param elem
     *            an element from that VecInt
     */
    public void remove(int elem) {
        // assert size() > 0;
        int j = 0;
        for (; this.myarray[j] != elem; j++) {
            if (j == size())
                throw new NoSuchElementException();
        }
        System.arraycopy(this.myarray, j + 1, this.myarray, j, size() - j - 1);
        pop();
    }

    /**
     * Delete the ith element of the vector. The latest element of the vector
     * replaces the removed element at the ith indexer.
     * 
     * @param i
     *            the indexer of the element in the vector
     * @return the former ith element of the vector that is now removed from the
     *         vector
     */
    public int delete(int i) {
        // assert i >= 0 && i < nbelem;
        int ith = this.myarray[i];
        this.myarray[i] = this.myarray[--this.nbelem];
        return ith;
    }

    private int nbelem;

    private int[] myarray;

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.int#toString()
     */
    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        for (int i = 0; i < this.nbelem - 1; i++) {
            stb.append(this.myarray[i]);
            stb.append(","); //$NON-NLS-1$
        }
        if (this.nbelem > 0) {
            stb.append(this.myarray[this.nbelem - 1]);
        }
        return stb.toString();
    }

    void selectionSort(int from, int to) {
        int i, j, besti;
        int tmp;

        for (i = from; i < to - 1; i++) {
            besti = i;
            for (j = i + 1; j < to; j++) {
                if (this.myarray[j] < this.myarray[besti]) {
                    besti = j;
                }
            }
            tmp = this.myarray[i];
            this.myarray[i] = this.myarray[besti];
            this.myarray[besti] = tmp;
        }
    }

    void sort(int from, int to) {
        int width = to - from;
        if (width <= 15) {
            selectionSort(from, to);
        } else {
            final int[] locarray = this.myarray;
            int pivot = locarray[width / 2 + from];
            int tmp;
            int i = from - 1;
            int j = to;

            for (;;) {
                do {
                    i++;
                } while (locarray[i] < pivot);
                do {
                    j--;
                } while (pivot < locarray[j]);

                if (i >= j) {
                    break;
                }

                tmp = locarray[i];
                locarray[i] = locarray[j];
                locarray[j] = tmp;
            }

            sort(from, i);
            sort(i, to);
        }
    }

    /**
     * sort the vector using a custom quicksort.
     */
    public void sort() {
        sort(0, this.nbelem);
    }

    public void sortUnique() {
        int i, j;
        int last;
        if (this.nbelem == 0) {
            return;
        }

        sort(0, this.nbelem);
        i = 1;
        int[] locarray = this.myarray;
        last = locarray[0];
        for (j = 1; j < this.nbelem; j++) {
            if (last < locarray[j]) {
                last = locarray[i] = locarray[j];
                i++;
            }
        }

        this.nbelem = i;
    }

    /**
     * Two vectors are equals iff they have the very same elements in the order.
     * 
     * @param obj
     *            an object
     * @return true iff obj is a VecInt and has the same elements as this vector
     *         at each index.
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof IVecInt) {
            IVecInt v = (IVecInt) obj;
            if (v.size() != this.nbelem) {
                return false;
            }
            for (int i = 0; i < this.nbelem; i++) {
                if (v.get(i) != this.myarray[i]) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        long sum = 0;
        for (int i = 0; i < this.nbelem; i++) {
            sum += this.myarray[i];
        }
        return (int) sum / this.nbelem;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IVecInt2#pushAll(org.sat4j.specs.IVecInt2)
     */
    public void pushAll(IVecInt vec) {
        VecInt nvec = (VecInt) vec;
        int nsize = this.nbelem + nvec.nbelem;
        ensure(nsize);
        System.arraycopy(nvec.myarray, 0, this.myarray, this.nbelem,
                nvec.nbelem);
        this.nbelem = nsize;
    }

    /**
     * to detect that the vector is a subset of another one. Note that the
     * method assumes that the two vectors are sorted!
     * 
     * @param vec
     *            a vector
     * @return true iff the current vector is a subset of vec
     */
    public boolean isSubsetOf(VecInt vec) {
        int i = 0;
        int j = 0;
        while (i < this.nbelem && j < vec.nbelem) {
            while (j < vec.nbelem && vec.myarray[j] < this.myarray[i]) {
                j++;
            }
            if (j == vec.nbelem || this.myarray[i] != vec.myarray[j]) {
                return false;
            }
            i++;
        }
        return true;
    }

    public IteratorInt iterator() {
        return new IteratorInt() {
            private int i = 0;

            public boolean hasNext() {
                return this.i < VecInt.this.nbelem;
            }

            public int next() {
                if (this.i == VecInt.this.nbelem) {
                    throw new NoSuchElementException();
                }
                return VecInt.this.myarray[this.i++];
            }
        };
    }

    public boolean isEmpty() {
        return this.nbelem == 0;
    }

    /**
     * @since 2.1
     */
    public int[] toArray() {
        return this.myarray;
    }

    /**
     * @since 2.3.1
     * @author sroussel
     */
    public IVecInt[] subset(int cardinal) {
        List<IVecInt> liste = new ArrayList<IVecInt>();

        IVecInt[] result;

        if (cardinal == 1) {
            result = new VecInt[this.size()];
            for (int i = 0; i < this.size(); i++) {
                result[i] = new VecInt(new int[] { this.get(i) });
            }
            return result;
        }

        if (this.size() == 0) {
            result = new VecInt[0];
            return result;
        }

        VecInt subVec = new VecInt();
        VecInt newVec;
        this.copyTo(subVec);
        subVec.remove(this.get(0));

        for (IVecInt vecWithFirst : subVec.subset(cardinal - 1)) {
            newVec = new VecInt();
            vecWithFirst.copyTo(newVec);
            newVec.insertFirst(this.get(0));
            liste.add(newVec);
        }

        for (IVecInt vecWithoutFirst : subVec.subset(cardinal)) {
            liste.add(vecWithoutFirst);
        }

        result = new VecInt[liste.size()];
        for (int i = 0; i < liste.size(); i++) {
            result[i] = liste.get(i);
        }
        return result;
    }

    void selectionSort(int from, int to, Comparator<Integer> cmp) {
        int i, j, besti;
        int tmp;

        for (i = from; i < to - 1; i++) {
            besti = i;
            for (j = i + 1; j < to; j++) {
                if (cmp.compare(this.myarray[j], this.myarray[besti]) < 0) {
                    besti = j;
                }
            }
            tmp = this.myarray[i];
            this.myarray[i] = this.myarray[besti];
            this.myarray[besti] = tmp;
        }
    }

    void sort(int from, int to, Comparator<Integer> cmp) {
        int width = to - from;
        if (width <= 15) {
            selectionSort(from, to, cmp);
        } else {
            int pivot = this.myarray[width / 2 + from];
            int tmp;
            int i = from - 1;
            int j = to;

            for (;;) {
                do {
                    i++;
                } while (cmp.compare(this.myarray[i], pivot) < 0);
                do {
                    j--;
                } while (cmp.compare(pivot, this.myarray[j]) < 0);

                if (i >= j) {
                    break;
                }

                tmp = this.myarray[i];
                this.myarray[i] = this.myarray[j];
                this.myarray[j] = tmp;
            }

            sort(from, i, cmp);
            sort(i, to, cmp);
        }
    }

    /**
     * Sort the vector according to a given order.
     * 
     * @param comparator
     *            a way to order the integers of that vector.
     */
    public void sort(Comparator<Integer> comparator) {
        sort(0, this.nbelem, comparator);
    }

    @Override
    public IVecInt clone() {
        IVecInt cloned = new VecInt(this.size());
        this.copyTo(cloned);
        return cloned;
    }

    /**
     * Alternative way to create a vector, the Java 9+ way.
     * 
     * @param values
     *            an arbitrary number of values
     * @return a new vector with those values
     * @since 2.3.6
     */
    public static VecInt of(int... values) {
        return new VecInt(values);
    }

    /**
     * Alternative way to create a vector, the Java 9+ way, from a standard Java
     * collection.
     * 
     * @param values
     *            a collection with an arbitrary number of values
     * @return a new vector with those values
     * @since 2.3.6
     */
    public static VecInt of(Collection<Integer> values) {
        VecInt v = new VecInt(values.size());
        for (Integer i : values) {
            v.push(i);
        }
        return v;
    }
}
