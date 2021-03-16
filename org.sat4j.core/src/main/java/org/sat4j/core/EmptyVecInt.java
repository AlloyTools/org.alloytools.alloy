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

import java.util.Comparator;

import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

final class EmptyVecInt implements IVecInt {
    /**
    	 * 
    	 */
    private static final long serialVersionUID = 1L;

    public int size() {
        return 0;
    }

    public void shrink(int nofelems) {
    }

    public void shrinkTo(int newsize) {
    }

    public IVecInt pop() {
        throw new UnsupportedOperationException();
    }

    public void growTo(int newsize, int pad) {
    }

    public void ensure(int nsize) {
    }

    public IVecInt push(int elem) {
        throw new UnsupportedOperationException();
    }

    public void unsafePush(int elem) {
        throw new UnsupportedOperationException();
    }

    public void clear() {
    }

    public int last() {
        throw new UnsupportedOperationException();
    }

    public int get(int i) {
        throw new UnsupportedOperationException();
    }

    public void set(int i, int o) {
        throw new UnsupportedOperationException();
    }

    public boolean contains(int e) {
        return false;
    }

    public void copyTo(IVecInt copy) {
    }

    public void copyTo(int[] is) {
    }

    public void moveTo(IVecInt dest) {
    }

    public void moveTo2(IVecInt dest) {
    }

    public void moveTo(int[] dest) {
    }

    public void insertFirst(int elem) {
        throw new UnsupportedOperationException();
    }

    public void remove(int elem) {
        throw new UnsupportedOperationException();
    }

    public int delete(int i) {
        throw new UnsupportedOperationException();
    }

    public void sort() {
    }

    public void sortUnique() {
    }

    public int unsafeGet(int eleem) {
        throw new UnsupportedOperationException();
    }

    public int containsAt(int e) {
        throw new UnsupportedOperationException();
    }

    public int containsAt(int e, int from) {
        throw new UnsupportedOperationException();
    }

    public void moveTo(int dest, int source) {
        throw new UnsupportedOperationException();
    }

    public boolean isEmpty() {
        return true;
    }

    public IteratorInt iterator() {
        return new IteratorInt() {

            public boolean hasNext() {
                return false;
            }

            public int next() {
                throw new UnsupportedOperationException();
            }
        };
    }

    public int[] toArray() {
        throw new UnsupportedOperationException();
    }

    public int indexOf(int e) {
        return -1;
    }

    @Override
    public String toString() {
        return "[]";
    }

    public void moveTo(int sourceStartingIndex, int[] dest) {
        throw new UnsupportedOperationException();
    }

    public IVecInt[] subset(int cardinal) {
        return new IVecInt[0];
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof IVecInt) {
            return ((IVecInt) o).isEmpty();
        }
        return false;
    }

    @Override
    public int hashCode() {
        return 0;
    }

    public void sort(Comparator<Integer> comparator) {
    }

    @Override
    public IVecInt clone() {
        return new EmptyVecInt();
    }
}