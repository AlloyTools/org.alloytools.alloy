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
import java.util.Iterator;
import java.util.NoSuchElementException;

import org.sat4j.specs.IVec;

import junit.framework.TestCase;

/*
 * Created on 16 oct. 2003
 *
 */

/**
 * @author leberre
 * 
 */
public class VecTest extends TestCase {

    /**
     * Constructor for VecTest.
     * 
     * @param arg0
     */
    public VecTest(String arg0) {
        super(arg0);
    }

    /*
     * @see TestCase#setUp()
     */
    @Override
    protected void setUp() throws Exception {
        super.setUp();
        this.myvec = new Vec<Integer>();
    }

    /*
     * @see TestCase#tearDown()
     */
    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    /*
     * Test pour void Vec()
     */
    public void testVec() {
        IVec<Integer> vec = new Vec<Integer>();
        assertEquals(0, vec.size());
    }

    /*
     * Test pour void Vec(int)
     */
    public void testVecint() {
        IVec<Integer> vec = new Vec<Integer>(10, new Integer(0));
        assertEquals(new Integer(0), vec.last());
        assertEquals(10, vec.size());
    }

    /*
     * Test pour void Vec(int, Object)
     */
    public void testVecintObject() {
        Integer pad = new Integer(10);
        IVec<Integer> vec = new Vec<Integer>(10, pad);
        assertEquals(pad, vec.last());
        assertEquals(10, vec.size());

    }

    public void testSize() {
        assertEquals(0, this.myvec.size());
        this.myvec.push(null);
        assertEquals(1, this.myvec.size());
        this.myvec.push(null);
        assertEquals(2, this.myvec.size());
        this.myvec.pop();
        assertEquals(1, this.myvec.size());
        this.myvec.pop();
        assertEquals(0, this.myvec.size());
    }

    public void testShrink() {
        for (int i = 0; i < 15; i++) {
            this.myvec.push(new Integer(i));
        }
        assertEquals(15, this.myvec.size());
        this.myvec.shrink(10);
        assertEquals(5, this.myvec.size());
        assertEquals(new Integer(4), this.myvec.last());
        this.myvec.shrink(0);
        assertEquals(5, this.myvec.size());
        assertEquals(new Integer(4), this.myvec.last());
    }

    public void testShrinkTo() {
        for (int i = 0; i < 15; i++) {
            this.myvec.push(new Integer(i));
        }
        assertEquals(15, this.myvec.size());
        this.myvec.shrinkTo(10);
        assertEquals(10, this.myvec.size());
        assertEquals(new Integer(9), this.myvec.last());
        this.myvec.shrinkTo(10);
        assertEquals(10, this.myvec.size());
        assertEquals(new Integer(9), this.myvec.last());

    }

    public void testPop() {
        for (int i = 0; i < 15; i++) {
            this.myvec.push(new Integer(i));
        }
        assertEquals(15, this.myvec.size());
        this.myvec.pop();
        assertEquals(14, this.myvec.size());
        assertEquals(new Integer(13), this.myvec.last());
    }

    /*
     * Test pour void growTo(int)
     */
    public void testGrowToint() {
        assertEquals(0, this.myvec.size());
        this.myvec.growTo(12, null);
        assertEquals(12, this.myvec.size());
        assertNull(this.myvec.last());
        this.myvec.growTo(20, null);
        assertEquals(20, this.myvec.size());
        assertNull(this.myvec.last());
    }

    /*
     * Test pour void growTo(int, Object)
     */
    public void testGrowTointObject() {
        assertEquals(0, this.myvec.size());
        Integer douze = new Integer(12);
        this.myvec.growTo(12, douze);
        assertEquals(12, this.myvec.size());
        assertEquals(douze, this.myvec.last());
        Integer treize = new Integer(13);
        this.myvec.growTo(20, treize);
        assertEquals(20, this.myvec.size());
        assertEquals(treize, this.myvec.last());
    }

    /*
     * Test pour void push()
     */
    public void testPush() {
        assertEquals(0, this.myvec.size());
        for (int i = 0; i < 10; i++) {
            this.myvec.push(new Integer(0));
        }
        assertEquals(10, this.myvec.size());
        assertEquals(new Integer(0), this.myvec.last());
    }

    /*
     * Test pour void push(Object)
     */
    public void testPushObject() {
        Integer deux = new Integer(2);
        assertEquals(0, this.myvec.size());
        for (int i = 0; i < 10; i++) {
            this.myvec.push(deux);
        }
        assertEquals(10, this.myvec.size());
        assertEquals(deux, this.myvec.last());
    }

    public void testClear() {
        this.myvec.push(null);
        this.myvec.push(null);
        this.myvec.clear();
        assertEquals(0, this.myvec.size());
    }

    public void testLast() {
        for (int i = 0; i < 10; i++) {
            Integer myint = new Integer(i);
            this.myvec.push(myint);
            assertEquals(myint, this.myvec.last());
        }
    }

    public void testGet() {
        for (int i = 0; i < 10; i++) {
            Integer myint = new Integer(i);
            this.myvec.push(myint);
            assertEquals(myint, this.myvec.get(i));
        }
    }

    public void testCopyTo() {
        Vec<Integer> nvec = new Vec<Integer>();
        this.myvec.growTo(15, new Integer(15));
        this.myvec.copyTo(nvec);
        assertEquals(15, nvec.size());
        assertEquals(15, this.myvec.size());
        assertEquals(this.myvec.last(), nvec.last());

    }

    public void testMoveTo() {
        Vec<Integer> nvec = new Vec<Integer>();
        this.myvec.growTo(15, new Integer(15));
        this.myvec.moveTo(nvec);
        assertEquals(15, nvec.size());
        assertEquals(0, this.myvec.size());
        assertEquals(new Integer(15), nvec.last());
    }

    public void testSelectionSort() {
        Vec<Integer> nvec = new Vec<Integer>();
        for (int i = 30; i > 0; i--) {
            nvec.push(new Integer(i));
        }
        Comparator<Integer> comp = new DefaultComparator<Integer>();
        nvec.selectionSort(0, 30, comp);
        for (int i = 1; i <= 30; i++) {
            assertEquals(i, nvec.get(i - 1).intValue());
        }
    }

    public void testSort() {
        IVec<Integer> nvec = new Vec<Integer>();
        for (int i = 101; i > 0; i--) {
            nvec.push(new Integer(i));
        }
        nvec.push(new Integer(30));
        nvec.push(new Integer(40));
        Comparator<Integer> comp = new DefaultComparator<Integer>();
        nvec.sort(comp);
        for (int i = 1; i <= 30; i++) {
            assertEquals(i, nvec.get(i - 1).intValue());
        }
    }

    public void testSortEmpty() {
        IVec<Integer> nvec = new Vec<Integer>();
        Comparator<Integer> comp = new DefaultComparator<Integer>();
        nvec.sort(comp);
    }

    public void testSortUnique() {
        IVec<Integer> nvec = new Vec<Integer>();
        for (int i = 101; i > 0; i--) {
            nvec.push(new Integer(i));
        }
        nvec.push(new Integer(30));
        nvec.push(new Integer(40));
        nvec.push(new Integer(50));
        nvec.push(new Integer(55));
        nvec.push(new Integer(60));
        Comparator<Integer> comp = new DefaultComparator<Integer>();
        nvec.sortUnique(comp);
        for (int i = 1; i <= 101; i++) {
            assertEquals(i, nvec.get(i - 1).intValue());
        }
    }

    public void testDelete() {
        IVec<Integer> nvec = new Vec<Integer>();
        for (int i = 0; i < 100; i++) {
            nvec.push(new Integer(i));
        }
        assertEquals(new Integer(10), nvec.delete(10));
        assertEquals(new Integer(99), nvec.get(10));
        nvec.clear();
        nvec.push(new Integer(1));
        assertEquals(new Integer(1), nvec.delete(0));
    }

    public void testRemove() {
        IVec<Integer> nvec = new Vec<Integer>();
        for (int i = 0; i < 100; i++) {
            nvec.push(new Integer(i));
        }
        Integer toRemove = nvec.get(10);
        nvec.remove(toRemove);
        assertEquals(99, nvec.size());
        assertEquals(new Integer(11), nvec.get(10));
        nvec.clear();
        toRemove = new Integer(1);
        nvec.push(toRemove);
        assertEquals(1, nvec.size());
        nvec.remove(toRemove);
        assertEquals(0, nvec.size());
    }

    public void testRemoveFromLast() {
        IVec<Integer> nvec = new Vec<Integer>();
        for (int i = 0; i < 100; i++) {
            nvec.push(new Integer(i));
        }
        Integer toRemove = nvec.get(10);
        nvec.removeFromLast(toRemove);
        assertEquals(99, nvec.size());
        assertEquals(new Integer(11), nvec.get(10));
        nvec.clear();
        toRemove = new Integer(1);
        nvec.push(toRemove);
        assertEquals(1, nvec.size());
        nvec.removeFromLast(toRemove);
        assertEquals(0, nvec.size());
    }

    public void testEquals() {
        IVec<Integer> nvec = new Vec<Integer>(3, new Integer(2));
        IVec<Integer> vect = new Vec<Integer>(3, new Integer(2));
        IVec<Integer> vecf = new Vec<Integer>(4, new Integer(2));
        IVec<Integer> vecf2 = new Vec<Integer>(2, new Integer(2));
        IVec<Integer> vecf3 = new Vec<Integer>(3, new Integer(3));
        assertEquals(nvec, vect);
        assertFalse(nvec.equals(vecf));
        assertFalse(nvec.equals(vecf2));
        assertFalse(nvec.equals(vecf3));

    }

    public void testIterator() {
        Vec<String> str = new Vec<String>();
        str.push("titi");
        str.push("toto");
        str.push("tata");
        Iterator<String> it = str.iterator();
        assertTrue(it.hasNext());
        assertEquals("titi", it.next());
        assertTrue(it.hasNext());
        assertEquals("toto", it.next());
        assertTrue(it.hasNext());
        assertEquals("tata", it.next());
        assertFalse(it.hasNext());
    }

    public void testNoSuchElementException() {
        Vec<String> str = new Vec<String>();
        Iterator<String> it = str.iterator();
        assertFalse(it.hasNext());
        try {
            it.next();
            fail();
        } catch (NoSuchElementException e) {
            // ok
        }
    }

    private IVec<Integer> myvec;

}
