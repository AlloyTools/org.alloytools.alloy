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
package org.sat4j.specs;

import java.io.Serializable;
import java.util.Comparator;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * An abstraction on the type of vector used in the library.
 * 
 * @author leberre
 */
public interface IVec<T> extends Serializable, Cloneable {

    /**
     * @return the number of elements contained in the vector
     */
    int size();

    /**
     * Remove nofelems from the Vector. It is assumed that the number of
     * elements to remove is smaller or equals to the current number of elements
     * in the vector
     * 
     * @param nofelems
     *            the number of elements to remove.
     */
    void shrink(int nofelems);

    /**
     * reduce the Vector to exactly newsize elements
     * 
     * @param newsize
     *            the new size of the vector.
     */
    void shrinkTo(final int newsize);

    /**
     * Pop the last element on the stack. It is assumed that the stack is not
     * empty!
     */
    void pop();

    void growTo(final int newsize, final T pad);

    void ensure(final int nsize);

    IVec<T> push(final T elem);

    /**
     * To push an element in the vector when you know you have space for it.
     * 
     * @param elem
     *            an element
     */
    void unsafePush(T elem);

    /**
     * Insert an element at the very begining of the vector. The former first
     * element is appended to the end of the vector in order to have a constant
     * time operation.
     * 
     * @param elem
     *            the element to put first in the vector.
     */
    void insertFirst(final T elem);

    void insertFirstWithShifting(final T elem);

    void clear();

    /**
     * return the latest element on the stack. It is assumed that the stack is
     * not empty!
     * 
     * @return the last (top) element on the stack
     */
    T last();

    T get(int i);

    void set(int i, T o);

    /**
     * Remove an element from the vector.
     * 
     * @param elem
     *            an element of the vector
     * @throws NoSuchElementException
     *             if elem is not found in the vector.
     */
    void remove(T elem);

    /**
     * Remove an element from the vector, starting with the last element.
     * 
     * @param elem
     *            an element of the vector
     * @throws NoSuchElementException
     *             if elem is not found in the vector.
     * @since 2.3.6
     */
    void removeFromLast(T elem);

    /**
     * Delete the ith element of the vector. The latest element of the vector
     * replaces the removed element at the ith indexer.
     * 
     * @param i
     *            the indexer of the element in the vector
     * @return the former ith element of the vector that is now removed from the
     *         vector
     */
    T delete(int i);

    /**
     * Copy the content of the vector to another vector.
     * 
     * THIS METHOD IS NOT SPECIALLY EFFICIENT. USE WITH CAUTION.
     * 
     * @param copy
     *            a non null vector
     */
    void copyTo(IVec<T> copy);

    /**
     * Copy the content of the vector to an array.
     * 
     * THIS METHOD IS NOT SPECIALLY EFFICIENT. USE WITH CAUTION.
     * 
     * @param dest
     *            a non null array, containing sufficient space to copy the
     *            content of the current vector, i.e.
     *            <code>dest.length &lt;= this.size()</code>.
     * @param <E>
     *            the type of the elements of the array. It must be a superclass
     *            of T.
     */
    <E> void copyTo(E[] dest);

    /**
     * Allow to access the internal representation of the vector as an array.
     * Note that only the content of index 0 to size() should be taken into
     * account. USE WITH CAUTION
     * 
     * @return the internal representation of the Vector as an array.
     */
    T[] toArray();

    /**
     * Move the content of the vector into dest. Note that the vector become
     * empty. The content of the vector is appended to dest.
     * 
     * @param dest
     *            the vector where top put the content of this vector
     */
    void moveTo(IVec<T> dest);

    /**
     * Move elements inside the vector. The content of the method is equivalent
     * to: <code>vec[dest] = vec[source]</code>
     * 
     * @param dest
     *            the index of the destination
     * @param source
     *            the index of the source
     */
    void moveTo(int dest, int source);

    /*
     * @param comparator
     */
    void sort(Comparator<T> comparator);

    void sortUnique(Comparator<T> comparator);

    /**
     * To know if a vector is empty
     * 
     * @return true iff the vector is empty.
     * @since 1.6
     */
    boolean isEmpty();

    Iterator<T> iterator();

    /**
     * 
     * @param element
     *            an object
     * @return true iff element is found in the vector.
     * @since 2.1
     */
    boolean contains(T element);

    /**
     * @param element
     *            an object
     * @return the index of the element if it is found in the vector, else -1.
     * @since 2.2
     */
    int indexOf(T element);

    /**
     * Clone the object.
     * 
     * @return a copy of the object.
     * @since 2.3.6
     */
    IVec<T> clone();
}
