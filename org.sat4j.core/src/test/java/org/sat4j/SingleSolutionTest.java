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
package org.sat4j;

import junit.framework.TestCase;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.SingleSolutionDetector;

public class SingleSolutionTest extends TestCase {

    public SingleSolutionTest(String name) {
        super(name);
    }

    @Override
    protected void setUp() throws Exception {
        this.solver = SolverFactory.newDefault();
        this.detector = new SingleSolutionDetector(this.solver);
        this.detector.newVar(3);
    }

    /*
     * Test method for
     * 'org.sat4j.tools.SingleSolutionDetector.hasASingleSolution()'
     */
    public void testHasASingleSolution() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.detector.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable());
        assertFalse(this.detector.hasASingleSolution());
    }

    /*
     * Test method for
     * 'org.sat4j.tools.SingleSolutionDetector.hasASingleSolution()'
     */
    public void testHasNoSingleSolution() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.detector.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable());
        clause.clear();
        clause.push(-1).push(2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable());
        assertTrue(this.detector.hasASingleSolution());
        clause.clear();
        clause.push(1).push(-2);
        this.detector.addClause(clause);
        assertFalse(this.detector.isSatisfiable());
        try {
            assertFalse(this.detector.hasASingleSolution());
            fail();
        } catch (UnsupportedOperationException e) {
            // OK
        }
    }

    /*
     * Test method for
     * 'org.sat4j.tools.SingleSolutionDetector.hasASingleSolution()'
     */
    public void testHasNoSingleSolutionUNSAT() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.detector.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable());
        clause.clear();
        clause.push(-1).push(2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable());
        clause.clear();
        clause.push(1).push(-2);
        this.detector.addClause(clause);
        assertFalse(this.detector.isSatisfiable());
        try {
            assertFalse(this.detector.hasASingleSolution());
            fail();
        } catch (UnsupportedOperationException e) {
            // OK
        }
    }

    /*
     * Test method for
     * 'org.sat4j.tools.SingleSolutionDetector.hasASingleSolution(IVecInt)'
     */
    public void testHasASingleSolutionIVecInt() throws ContradictionException,
            TimeoutException {
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.detector.addClause(clause);
        IVecInt assumptions = new VecInt();
        assumptions.push(1);
        assertTrue(this.detector.isSatisfiable(assumptions));
        assertFalse(this.detector.hasASingleSolution(assumptions));
        clause.clear();
        clause.push(-1).push(2);
        this.detector.addClause(clause);
        assertTrue(this.detector.isSatisfiable(assumptions));
        assertTrue(this.detector.hasASingleSolution(assumptions));
        clause.clear();
        clause.push(-1).push(-2);
        this.detector.addClause(clause);
        assertFalse(this.detector.isSatisfiable(assumptions));
        try {
            assertFalse(this.detector.hasASingleSolution(assumptions));
            fail();
        } catch (UnsupportedOperationException e) {
            // OK
        }
    }

    private ISolver solver;

    private SingleSolutionDetector detector;
}
