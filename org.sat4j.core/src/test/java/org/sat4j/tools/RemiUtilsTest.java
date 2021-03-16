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
package org.sat4j.tools;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Testcase to check that the problem with unit clauses does no longer occurs.
 * 
 * Bug report from Sebastian Henneberg
 * 
 * 
 */
public class RemiUtilsTest {

    @Test
    public void testBugUnitClauses() throws ContradictionException,
            TimeoutException {
        ISolver solver1 = SolverFactory.newDefault();
        ISolver solver2 = SolverFactory.newDefault();
        ISolver solver3 = SolverFactory.newDefault();

        int[][] cnf1 = new int[][] { new int[] { 1 }, new int[] { 1, -2 },
                new int[] { 1, -3 }, new int[] { -1, 2 } };
        // A & (A v -B) & (A v -C) & (-A v B)
        // (-A v B) & (A v -B) & (A v -C) & A | using a different order
        int[][] cnf2 = new int[][] { new int[] { -1, 2 }, new int[] { 1, -2 },
                new int[] { 1, -3 }, new int[] { 1 } };
        // (-A v B) & (A v -B) & (A v -C) & A
        // (-A v C) & (A v -C) & (A v -B) & A | swap B and C (2 <-> 3)
        // (A v -B) & (-A v C) & (A v -C) & A | shift the first 3 clauses to the
        // right
        int[][] cnf3 = new int[][] { new int[] { 1, -2 }, new int[] { -1, 3 },
                new int[] { 1, -3 }, new int[] { 1 } };

        for (int[] is : cnf1) {
            solver1.addClause(new VecInt(is));
        }
        for (int[] is : cnf2) {
            solver2.addClause(new VecInt(is));
        }
        for (int[] is : cnf3) {
            solver3.addClause(new VecInt(is));
        }

        IVecInt vecInt1 = RemiUtils.backbone(solver1);
        assertEquals(vecInt1.size(), 2);
        assertTrue(vecInt1.contains(1));
        assertTrue(vecInt1.contains(2));

        IVecInt vecInt2 = RemiUtils.backbone(solver2);
        assertEquals(vecInt2.size(), 2);
        assertTrue(vecInt2.contains(1));
        assertTrue(vecInt2.contains(2));

        IVecInt vecInt3 = RemiUtils.backbone(solver3);
        assertEquals(vecInt3.size(), 2);
        assertTrue(vecInt3.contains(1));
        assertTrue(vecInt3.contains(3));
    }
}