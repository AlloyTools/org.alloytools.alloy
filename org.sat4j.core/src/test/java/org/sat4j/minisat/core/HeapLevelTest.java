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

import junit.framework.TestCase;

import org.sat4j.minisat.orders.ActivityBasedVariableComparator;
import org.sat4j.minisat.orders.LevelAndActivityVariableComparator;

public class HeapLevelTest extends TestCase {

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.setBounds(int)'
     */
    public void testSetBounds() {

    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.inHeap(int)'
     */
    public void testInHeap() {
        Heap heap = new Heap(new LevelAndActivityVariableComparator(
                new double[] { 0.0, 3.0, 9.0, 2.0 }, new int[] {
                        Integer.MAX_VALUE, 1, 1, 1 }));
        heap.setBounds(5);
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(1);
        assertTrue(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(2);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(3);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(2, heap.getmin());
        assertTrue(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(1, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(3, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));

    }

    public void testInHeap2() {
        Heap heap = new Heap(new LevelAndActivityVariableComparator(
                new double[] { 0.0, 3.0, 9.0, 2.0 }, new int[] {
                        Integer.MAX_VALUE, 1, 2, 3 }));
        heap.setBounds(5);
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(1);
        assertTrue(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(2);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(3);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(1, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(2, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(3, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));

    }

    public void testInHeap3() {
        Heap heap = new Heap(new LevelAndActivityVariableComparator(
                new double[] { 0.0, 3.0, 9.0, 2.0 }, new int[] {
                        Integer.MAX_VALUE, 3, 2, 1 }));
        heap.setBounds(5);
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(1);
        assertTrue(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(2);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        heap.insert(3);
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertTrue(heap.inHeap(3));
        assertEquals(3, heap.getmin());
        assertTrue(heap.inHeap(1));
        assertTrue(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        assertEquals(2, heap.getmin());
        assertTrue(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));
        assertEquals(1, heap.getmin());
        assertFalse(heap.inHeap(1));
        assertFalse(heap.inHeap(2));
        assertFalse(heap.inHeap(3));

    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.increase(int)'
     */
    public void testIncrease() {

    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.empty()'
     */
    public void testEmpty() {
        Heap heap = new Heap(new ActivityBasedVariableComparator(
                new double[] {}));
        assertTrue(heap.empty());
    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.insert(int)'
     */
    public void testInsert() {
        Heap heap = new Heap(new LevelAndActivityVariableComparator(
                new double[] { 0.0, 1.0, 1.0, 2.0 }, new int[] {
                        Integer.MAX_VALUE, 1, 1, 1 }));
        heap.setBounds(5);
        heap.insert(1);
        heap.insert(2);
        heap.insert(3);
        assertEquals(3, heap.getmin());
        assertEquals(1, heap.getmin());
        assertEquals(2, heap.getmin());
    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.getmin()'
     */
    public void testGetmin() {
        Heap heap = new Heap(new LevelAndActivityVariableComparator(
                new double[] { 0.0, 3.0, 9.0, 2.0 }, new int[] {
                        Integer.MAX_VALUE, 1, 1, 1 }));
        heap.setBounds(5);
        heap.insert(1);
        heap.insert(2);
        heap.insert(3);
        assertEquals(2, heap.getmin());
        assertEquals(1, heap.getmin());
        assertEquals(3, heap.getmin());
    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.heapProperty()'
     */
    public void testHeapProperty() {

    }

    /*
     * Test method for 'org.sat4j.minisat.core.Heap.heapProperty(int)'
     */
    public void testHeapPropertyInt() {

    }

}
