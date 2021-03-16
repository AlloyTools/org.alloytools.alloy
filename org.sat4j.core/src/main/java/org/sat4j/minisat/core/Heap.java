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

import org.sat4j.core.VecInt;
import org.sat4j.minisat.orders.VariableComparator;
import org.sat4j.specs.IVecInt;

/**
 * Heap implementation used to maintain the variables order in some heuristics.
 * 
 * @author daniel
 * 
 */
public final class Heap implements Serializable {

    /*
     * default serial version id
     */
    private static final long serialVersionUID = 1L;

    private static int left(int i) {
        return i << 1;
    }

    private static int right(int i) {
        return i << 1 ^ 1;
    }

    private static int parent(int i) {
        return i >> 1;
    }

    private final IVecInt heap = new VecInt(); // heap of ints

    private final IVecInt indices = new VecInt(); // int -> index in heap

    private final VariableComparator comparator;

    void percolateUp(int i) {
        int x = this.heap.get(i);
        int p = parent(i);
        while (i != 1 && comparator.preferredTo(x, this.heap.get(p))) {
            this.heap.set(i, this.heap.get(p));
            this.indices.set(this.heap.get(p), i);
            i = p;
            p = parent(p);
        }
        this.heap.set(i, x);
        this.indices.set(x, i);
    }

    void percolateDown(int i) {
        int x = this.heap.get(i);
        while (left(i) < this.heap.size()) {
            int child = right(i) < this.heap.size()
                    && comparator.preferredTo(this.heap.get(right(i)),
                            this.heap.get(left(i))) ? right(i) : left(i);
            if (!comparator.preferredTo(this.heap.get(child), x)) {
                break;
            }
            this.heap.set(i, this.heap.get(child));
            this.indices.set(this.heap.get(i), i);
            i = child;
        }
        this.heap.set(i, x);
        this.indices.set(x, i);
    }

    boolean ok(int n) {
        return n >= 0 && n < this.indices.size();
    }

    public Heap(VariableComparator comparator) { // NOPMD
        this.comparator = comparator;
        this.heap.push(-1);
    }

    public void setBounds(int size) {
        assert size >= 0;
        this.indices.growTo(size, 0);
    }

    public boolean inHeap(int n) {
        assert ok(n);
        return this.indices.get(n) != 0;
    }

    public void increase(int n) {
        assert ok(n);
        assert inHeap(n);
        percolateUp(this.indices.get(n));
    }

    public boolean empty() {
        return this.heap.size() == 1;
    }

    public int size() {
        return this.heap.size() - 1;
    }

    public int get(int i) {
        int r = this.heap.get(i);
        this.heap.set(i, this.heap.last());
        this.indices.set(this.heap.get(i), i);
        this.indices.set(r, 0);
        this.heap.pop();
        if (this.heap.size() > 1) {
            percolateDown(1);
        }
        return r;
    }

    public void insert(int n) {
        assert ok(n);
        this.indices.set(n, this.heap.size());
        this.heap.push(n);
        percolateUp(this.indices.get(n));
    }

    public int getmin() {
        return get(1);
    }

    public boolean heapProperty() {
        return heapProperty(1);
    }

    public boolean heapProperty(int i) {
        return i >= this.heap.size()
                || (parent(i) == 0 || !comparator.preferredTo(this.heap.get(i),
                        this.heap.get(parent(i)))) && heapProperty(left(i))
                && heapProperty(right(i));
    }

}
