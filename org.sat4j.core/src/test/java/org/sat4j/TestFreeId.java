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

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

public class TestFreeId {

    private ISolver solver;

    @Before
    public void setUp() {
        this.solver = SolverFactory.newDefault();
    }

    @Test
    public void testEmptySolver() {
        assertEquals(1, this.solver.nextFreeVarId(false));
        this.solver.newVar(100);
        assertEquals(101, this.solver.nextFreeVarId(false));
    }

    @Test
    public void testIncrementalFeed() throws ContradictionException {
        assertEquals(1, this.solver.nextFreeVarId(false));
        IVecInt clause = new VecInt();
        clause.push(3).push(-5);
        this.solver.addClause(clause);
        assertEquals(6, this.solver.nextFreeVarId(false));
        clause.clear();
        clause.push(1).push(-2);
        this.solver.addClause(clause);
        assertEquals(6, this.solver.nextFreeVarId(false));
        clause.clear();
        clause.push(1000).push(-31);
        this.solver.addClause(clause);
        assertEquals(1001, this.solver.nextFreeVarId(false));
    }

    @Test
    public void testReserveParameter() {
        assertEquals(1, this.solver.nextFreeVarId(false));
        assertEquals(1, this.solver.nextFreeVarId(false));
        assertEquals(1, this.solver.nextFreeVarId(false));
        assertEquals(1, this.solver.nextFreeVarId(false));
        assertEquals(1, this.solver.nextFreeVarId(true));
        assertEquals(2, this.solver.nextFreeVarId(true));
        assertEquals(3, this.solver.nextFreeVarId(false));
        assertEquals(3, this.solver.nextFreeVarId(false));
    }
}
