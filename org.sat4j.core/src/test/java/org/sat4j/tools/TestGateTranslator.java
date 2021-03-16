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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class TestGateTranslator {

    private ISolver solver;
    private GateTranslator gator;

    @Before
    public void startUp() {
        this.solver = SolverFactory.newDefault();
        this.gator = new GateTranslator(this.solver);
    }

    @Test
    public void testTwoValues() throws ContradictionException {
        IVecInt literals = new VecInt().push(1).push(2);
        IVec<BigInteger> coefs = new Vec<BigInteger>().push(
                BigInteger.valueOf(3)).push(BigInteger.valueOf(6));
        IVecInt result = new VecInt();
        this.gator.optimisationFunction(literals, coefs, result);
        System.out.println(result);
        assertEquals(4, result.size());

    }

    @Test
    public void testSATIfThen1() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertTrue(gator.isSatisfiable(new VecInt(new int[] { 1, 2, 3 })));

    }

    @Test
    public void testSATIfThen2() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertFalse(gator.isSatisfiable(new VecInt(new int[] { 1, 2, -3 })));
    }

    @Test
    public void testSATIfThen3() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertTrue(gator.isSatisfiable(new VecInt(new int[] { 1, -2, 3 })));
    }

    @Test
    public void testSATIfThen() throws ContradictionException, TimeoutException {
        gator.it(1, 2, 3);
        assertTrue(gator.isSatisfiable(new VecInt(new int[] { 1, -2, -3 })));
    }

    @Test
    public void testSATIfThen5() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertFalse(gator.isSatisfiable(new VecInt(new int[] { -1, 2, 3 })));
    }

    @Test
    public void testSATIfThen6() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertTrue(gator.isSatisfiable(new VecInt(new int[] { -1, 2, -3 })));
    }

    @Test
    public void testSATIfThen7() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertFalse(gator.isSatisfiable(new VecInt(new int[] { -1, -2, 3 })));
    }

    @Test
    public void testSATIfThen8() throws ContradictionException,
            TimeoutException {
        gator.it(1, 2, 3);
        assertFalse(gator.isSatisfiable(new VecInt(new int[] { -1, -2, -3 })));
    }
}
