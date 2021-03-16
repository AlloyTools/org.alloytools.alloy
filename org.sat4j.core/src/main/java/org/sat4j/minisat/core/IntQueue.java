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
package org.sat4j.minisat.core;

import java.io.Serializable;

/**
 * Implementation of a queue.
 * 
 * Formerly used in the solver to maintain unit literals for unit propagation.
 * No longer used currently.
 * 
 * @author leberre
 */
public final class IntQueue implements Serializable {

    private static final long serialVersionUID = 1L;

    private static final int INITIAL_QUEUE_CAPACITY = 10;

    /**
     * Add an element to the queue. The queue is supposed to be large enough for
     * that!
     * 
     * @param x
     *            the element to add
     */
    public void insert(final int x) {
        // ensure(size + 1);
        assert this.size < this.myarray.length;
        this.myarray[this.size++] = x;
    }

    /**
     * returns the nexdt element in the queue. Unexpected results if the queue
     * is empty!
     * 
     * @return the firsst element on the queue
     */
    public int dequeue() {
        assert this.first < this.size;
        return this.myarray[this.first++];
    }

    /**
     * Vide la queue
     */
    public void clear() {
        this.size = 0;
        this.first = 0;
    }

    /**
     * Pour connaitre la taille de la queue.
     * 
     * @return le nombre d'elements restant dans la queue
     */
    public int size() {
        return this.size - this.first;
    }

    /**
     * Utilisee pour accroitre dynamiquement la taille de la queue.
     * 
     * @param nsize
     *            la taille maximale de la queue
     */
    public void ensure(final int nsize) {
        if (nsize >= this.myarray.length) {
            int[] narray = new int[Math.max(nsize, this.size * 2)];
            System.arraycopy(this.myarray, 0, narray, 0, this.size);
            this.myarray = narray;
        }
    }

    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        stb.append(">"); //$NON-NLS-1$
        for (int i = this.first; i < this.size - 1; i++) {
            stb.append(this.myarray[i]);
            stb.append(" "); //$NON-NLS-1$
        }
        if (this.first != this.size) {
            stb.append(this.myarray[this.size - 1]);
        }
        stb.append("<"); //$NON-NLS-1$
        return stb.toString();
    }

    private int[] myarray = new int[INITIAL_QUEUE_CAPACITY];

    private int size = 0;

    private int first = 0;

}
