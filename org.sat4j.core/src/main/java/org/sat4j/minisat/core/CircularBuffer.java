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
 * Create a circular buffer of a given capacity allowing to compute efficiently
 * the mean of the values storied.
 * 
 * @author leberre
 * 
 */
public class CircularBuffer implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    private final int[] values;
    private int index = 0;
    private long sum = 0;
    private boolean full = false;

    public CircularBuffer(int capacity) {
        this.values = new int[capacity];
    }

    public void push(int value) {
        if (!this.full) {
            this.values[this.index++] = value;
            this.sum += value;
            if (this.index == this.values.length) {
                this.full = true;
                this.index = -1;
            }
            return;
        }
        this.index++;
        if (this.index == this.values.length) {
            this.index = 0;
        }
        // buffer full, overwrite
        this.sum -= this.values[this.index];
        this.values[this.index] = value;
        this.sum += value;
    }

    public long average() {
        if (this.full) {
            return this.sum / this.values.length;
        }
        if (this.index == 0) {
            return 0;
        }
        return this.sum / this.index;
    }

    public void clear() {
        this.index = 0;
        this.full = false;
        this.sum = 0;
    }

    public boolean isFull() {
        return this.full;
    }
}
