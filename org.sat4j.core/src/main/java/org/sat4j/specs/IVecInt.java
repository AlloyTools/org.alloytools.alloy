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
import java.util.NoSuchElementException;

/**
 * An abstraction for the vector of int used on the library.
 * 
 * @author leberre
 */
public interface IVecInt extends Serializable, Cloneable {

    int size();

    /**
     * Remove the latest nofelems elements from the vector.
     * 
     * @param nofelems
     *            the number of elements to remove.
     */
    void shrink(int nofelems);

    /**
     * Reduce the vector to a given number of elements.
     * 
     * All the elements after the limit are remove from the vector.
     * 
     * @param newsize
     *            the new size of the vector
     */
    void shrinkTo(int newsize);

    /**
     * Removes the last element of the vector.
     * 
     * If the vector is empty, does nothing.
     * 
     * @return the vector itself, for method chaining.
     */
    IVecInt pop();

    void growTo(int newsize, final int pad);

    void ensure(int nsize);

    IVecInt push(int elem);

    /**
     * Push the element in the Vector without verifying if there is room for it.
     * USE WITH CAUTION!
     * 
     * @param elem
     *            an integer
     */
    void unsafePush(int elem);

    int unsafeGet(int eleem);

    void clear();

    int last();

    int get(int i);

    void set(int i, int o);

    boolean contains(int e);

    /**
     * Retrieve the index of an element.
     * 
     * @param e
     *            an element
     * @return the index of the element, -1 if not found
     * @since 2.2
     */
    int indexOf(int e);

    /**
     * returns the index of the first occurrence of e, else -1.
     * 
     * @param e
     *            an integer
     * @return the index i such that <code>get(i)==e, else -1</code>.
     */
    int containsAt(int e);

    /**
     * returns the index of the first occurrence of e occurring after from
     * (excluded), else -1.
     * 
     * @param e
     *            an integer
     * @param from
     *            the index to start from (excluded).
     * @return the index i such that
     *         <code>i&gt;from and get(i)==e, else -1</code>
     */
    int containsAt(int e, int from);

    /**
     * Copy the content of the vector to another vector.
     * 
     * THIS METHOD IS NOT SPECIALLY EFFICIENT. USE WITH CAUTION.
     * 
     * @param copy
     *            a non null vector of integers
     */
    void copyTo(IVecInt copy);

    /**
     * Copy the content of the vector to an array.
     * 
     * THIS METHOD IS NOT SPECIALLY EFFICIENT. USE WITH CAUTION.
     * 
     * @param is
     *            a non null array, containing sufficient space to copy the
     *            content of the current vector, i.e.
     *            <code>is.length &gt;= this.size()</code>.
     */
    void copyTo(int[] is);

    /**
     * Move the content of the current vector to a destination one, in constant
     * time.
     * 
     * @param dest
     *            a vector of integer.
     */
    void moveTo(IVecInt dest);

    void moveTo(int sourceStartingIndex, int[] dest);

    void moveTo2(IVecInt dest);

    void moveTo(int[] dest);

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

    /**
     * Insert an element at the very begining of the vector. The former first
     * element is appended to the end of the vector in order to have a constant
     * time operation.
     * 
     * @param elem
     *            the element to put first in the vector.
     */
    void insertFirst(final int elem);

    /**
     * Remove an element from the vector.
     * 
     * @param elem
     *            an element of the vector
     * @throws NoSuchElementException
     *             if elem is not found in the vector.
     */
    void remove(int elem);

    /**
     * Delete the ith element of the vector. The latest element of the vector
     * replaces the removed element at the ith indexer.
     * 
     * @param i
     *            the indexer of the element in the vector
     * @return the former ith element of the vector that is now removed from the
     *         vector
     */
    int delete(int i);

    void sort();

    void sort(Comparator<Integer> comparator);

    void sortUnique();

    /**
     * To know if a vector is empty
     * 
     * @return true iff the vector is empty.
     * @since 1.6
     */
    boolean isEmpty();

    IteratorInt iterator();

    /**
     * Allow to access the internal representation of the vector as an array.
     * Note that only the content of index 0 to size() should be taken into
     * account. USE WITH CAUTION
     * 
     * @return the internal representation of the Vector as an array.
     * @since 2.1
     */
    int[] toArray();

    /**
     * Compute all subsets of cardinal k of the vector.
     * 
     * @param k
     *            a cardinal (<code>k&lt;= vec.size()</code>)
     * @return an array of IVectInt representing each a k-subset of this vector.
     * @author sroussel
     * @since 2.3.1
     */
    IVecInt[] subset(int k);

    /**
     * Clone the object.
     * 
     * @return a copy of the object.
     * @since 2.3.6
     */
    IVecInt clone();
}
