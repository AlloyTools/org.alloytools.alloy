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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

public abstract class AbstractXplainTest<T extends ISolver, G extends Xplain<T>> {

    protected G solver;

    protected abstract G getXplain();

    @Before
    public void startUp() {
        this.solver = getXplain();
    }

    @Test
    public void testGlobalInconsistency() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(2);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(4, explanation.size());
    }

    @Test
    public void testGlobalInconsistencyIndex() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(2);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        int[] explanation = this.solver.minimalExplanation();
        assertEquals(4, explanation.length);
        assertEquals(1, explanation[0]);
        assertEquals(2, explanation[1]);
        assertEquals(3, explanation[2]);
        assertEquals(4, explanation[3]);

    }

    @Test
    public void testAlmostGlobalInconsistency() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        IConstr c3 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        IConstr c4 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(4, explanation.size());
        assertTrue(explanation.contains(c1));
        assertTrue(explanation.contains(c2));
        assertTrue(explanation.contains(c3));
        assertTrue(explanation.contains(c4));
    }

    @Test
    public void testAlmostGlobalInconsistencyIndex()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        int[] explanation = this.solver.minimalExplanation();
        assertEquals(4, explanation.length);
        assertEquals(1, explanation[0]);
        assertEquals(2, explanation[1]);
        assertEquals(3, explanation[2]);
        assertEquals(4, explanation[3]);
    }

    @Test
    public void testAlmostGlobalInconsistencyII()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        IConstr c4 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        IConstr c5 = this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(4, explanation.size());
        assertTrue(explanation.contains(c1));
        assertTrue(explanation.contains(c2));
        assertTrue(explanation.contains(c4));
        assertTrue(explanation.contains(c5));
    }

    @Test
    public void testAlmostGlobalInconsistencyIIIndex()
            throws ContradictionException, TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        int[] explanation = this.solver.minimalExplanation();
        assertEquals(4, explanation.length);
        assertEquals(1, explanation[0]);
        assertEquals(2, explanation[1]);
        assertEquals(4, explanation[2]);
        assertEquals(5, explanation[3]);
    }

    @Test
    public void testTheCaseOfTwoMUSes() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(4);
        IVecInt clause = new VecInt();
        clause.push(1).push(2);
        IConstr c1 = this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(-2);
        IConstr c2 = this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(4);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-4);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(4, explanation.size());
        assertTrue(explanation.contains(c1));
        assertTrue(explanation.contains(c2));
    }

    @Test
    public void testEclipseTestCase() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(3);
        IVecInt clause = new VecInt();
        clause.push(-1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(2);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(3, explanation.size());
    }

    @Test
    public void testEclipseTestCase2() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(4);
        IVecInt clause = new VecInt();
        clause.push(-1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-2).push(-3);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-4).push(1);
        this.solver.addClause(clause);
        clause.clear();
        IVecInt assump = new VecInt();
        assump.push(4);
        assertFalse(this.solver.isSatisfiable(assump));
        Collection<IConstr> explanation = this.solver.explain();
        assertEquals(4, explanation.size());
    }

    @Test
    public void testDavidTestCase() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(2);
        IVecInt clause = new VecInt();
        clause.push(1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(1).push(2);
        this.solver.addClause(clause);
        clause.clear();
        clause.push(-1).push(-2);
        this.solver.addClause(clause);
        clause.clear();
        assertFalse(this.solver.isSatisfiable());
        Collection<IConstr> explanation = this.solver.explain();
        System.out.println(explanation);
        assertTrue(explanation.size() == 2 || explanation.size() == 3);
    }
}
