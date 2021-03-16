package org.sat4j.core;

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
import java.util.Comparator;
import java.util.Iterator;

import org.sat4j.specs.IVec;

/**
 * Utility class to allow Read Only access to an {@link IVec}.
 * 
 * @author daniel
 * 
 * @param <T>
 *            the type of the container.
 */
public final class ReadOnlyVec<T> implements IVec<T> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final IVec<T> vec;

    public ReadOnlyVec(IVec<T> vec) {
        this.vec = vec;
    }

    public void clear() {
        throw new UnsupportedOperationException();
    }

    public void copyTo(IVec<T> copy) {
        this.vec.copyTo(copy);
    }

    public <E> void copyTo(E[] dest) {
        this.vec.copyTo(dest);
    }

    public T delete(int i) {
        throw new UnsupportedOperationException();
    }

    public void ensure(int nsize) {
        throw new UnsupportedOperationException();

    }

    public T get(int i) {
        return this.vec.get(i);
    }

    public void growTo(int newsize, T pad) {
        throw new UnsupportedOperationException();
    }

    public void insertFirst(T elem) {
        throw new UnsupportedOperationException();
    }

    public void insertFirstWithShifting(T elem) {
        throw new UnsupportedOperationException();
    }

    public boolean isEmpty() {
        return this.vec.isEmpty();
    }

    public Iterator<T> iterator() {
        return this.vec.iterator();
    }

    public T last() {
        return this.vec.last();
    }

    public void moveTo(IVec<T> dest) {
        throw new UnsupportedOperationException();
    }

    public void moveTo(int dest, int source) {
        throw new UnsupportedOperationException();
    }

    public void pop() {
        throw new UnsupportedOperationException();
    }

    public IVec<T> push(T elem) {
        throw new UnsupportedOperationException();
    }

    public void remove(T elem) {
        throw new UnsupportedOperationException();
    }

    public void removeFromLast(T elem) {
        throw new UnsupportedOperationException();
    }

    public void set(int i, T o) {
        throw new UnsupportedOperationException();
    }

    public void shrink(int nofelems) {
        throw new UnsupportedOperationException();
    }

    public void shrinkTo(int newsize) {
        throw new UnsupportedOperationException();
    }

    public int size() {
        return this.vec.size();
    }

    public void sort(Comparator<T> comparator) {
        throw new UnsupportedOperationException();
    }

    public void sortUnique(Comparator<T> comparator) {
        throw new UnsupportedOperationException();
    }

    @SuppressWarnings("unchecked")
    public T[] toArray() {
        T[] array = (T[]) new Object[this.vec.size()];
        this.vec.copyTo(array);
        return array;
    }

    public void unsafePush(T elem) {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.1
     */
    public boolean contains(T element) {
        return this.vec.contains(element);
    }

    /**
     * @since 2.2
     */
    public int indexOf(T element) {
        return this.vec.indexOf(element);
    }

    @Override
    public String toString() {
        return this.vec.toString();
    }

    @Override
    public int hashCode() {
        return this.vec.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        return this.vec.equals(obj);
    }

    @Override
    public IVec<T> clone() {
        IVec<T> cloned = new Vec<T>(this.size());
        this.copyTo(cloned);
        return new ReadOnlyVec<T>(cloned);
    }
}
