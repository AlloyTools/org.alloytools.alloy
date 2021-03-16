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
package org.sat4j.minisat.constraints;

import junit.framework.TestCase;

import org.sat4j.minisat.constraints.cnf.Lits;
import org.sat4j.minisat.core.ILits;

/*
 * Created on 30 oct. 2003
 *
 */

/**
 * @author leberre
 * 
 */
public class LitTest extends TestCase {

    private ILits lits;

    /**
     * Constructor for LitTest.
     * 
     * @param arg0
     */
    public LitTest(String arg0) {
        super(arg0);
    }

    /*
     * @see TestCase#setUp()
     */
    @Override
    protected void setUp() throws Exception {
        super.setUp();
        this.lits = new Lits();
    }

    public void testNot() {
        this.lits.ensurePool(5);
        int lit = this.lits.getFromPool(-5);
        assertEquals(this.lits.getFromPool(5), lit ^ 1);
    }

    public void testVar() {
        this.lits.ensurePool(10);
        int lit = this.lits.getFromPool(-5);
        assertEquals(5, lit >> 1);
        lit = this.lits.getFromPool(10);
        assertEquals(10, lit >> 1);

    }

    /*
     * Test pour boolean equals(Object)
     */
    public void testEqualsObject() {
        this.lits.ensurePool(3);
        int lit = this.lits.getFromPool(-3);
        assertEquals(this.lits.getFromPool(-3), lit);
        assertEquals(this.lits.getFromPool(3), lit ^ 1);
        assertFalse(this.lits.getFromPool(1) == this.lits.getFromPool(2));
    }

    /*
     * Test pour String toString()
     */
    public void testToString() {
        this.lits.ensurePool(3);
        int lit = this.lits.getFromPool(-3);
        assertEquals("-3", Lits.toString(lit));
        assertEquals("3", Lits.toString(lit ^ 1));
    }

    public void testTruthValue() {
        this.lits.ensurePool(3);
        int lit = this.lits.getFromPool(-2);
        assertTrue(this.lits.isUnassigned(lit));
        assertTrue(this.lits.isUnassigned(lit ^ 1));
        this.lits.satisfies(lit);
        assertTrue(this.lits.isSatisfied(lit));
        assertFalse(this.lits.isFalsified(lit));
        assertFalse(this.lits.isUnassigned(lit));
        assertFalse(this.lits.isSatisfied(lit ^ 1));
        assertTrue(this.lits.isFalsified(lit ^ 1));
        assertFalse(this.lits.isUnassigned(lit ^ 1));
        this.lits.unassign(lit);
        assertTrue(this.lits.isUnassigned(lit));
        assertTrue(this.lits.isUnassigned(lit ^ 1));

    }

}
