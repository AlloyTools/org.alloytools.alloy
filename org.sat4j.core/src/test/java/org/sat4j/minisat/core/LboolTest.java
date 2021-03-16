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

import org.sat4j.specs.Lbool;

/*
 * Created on 2 nov. 2003
 *
 */

/**
 * @author leberre
 * 
 */
public class LboolTest extends TestCase {

    /**
     * Constructor for LboolTest.
     * 
     * @param arg0
     */
    public LboolTest(String arg0) {
        super(arg0);
    }

    public void testNot() {
        assertEquals(Lbool.FALSE, Lbool.TRUE.not());
        assertEquals(Lbool.TRUE, Lbool.FALSE.not());
        assertEquals(Lbool.UNDEFINED, Lbool.UNDEFINED.not());
    }

    /*
     * Test pour boolean equals(Object)
     */
    public void testEqualsObject() {
        assertEquals(Lbool.FALSE, Lbool.FALSE);
        assertNotSame(Lbool.FALSE, Lbool.TRUE);
        assertNotSame(Lbool.FALSE, Lbool.UNDEFINED);
        assertNotSame(Lbool.TRUE, Lbool.UNDEFINED);
    }

    /*
     * Test pour String toString()
     */
    public void testToString() {
        assertEquals("U", Lbool.UNDEFINED.toString());
        assertEquals("T", Lbool.TRUE.toString());
        assertEquals("F", Lbool.FALSE.toString());
    }

}
