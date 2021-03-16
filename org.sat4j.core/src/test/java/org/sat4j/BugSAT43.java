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

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

public class BugSAT43 {

    @Test
    public void testNoDeclaredVariables() throws ContradictionException,
            TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        assertEquals(0, solver.nVars());
        assertEquals(0, solver.realNumberOfVariables());
        for (int i = 0; i < 10; i++) {
            solver.nextFreeVarId(true);
        }
        assertEquals(10, solver.nVars());
        assertEquals(10, solver.realNumberOfVariables());
        solver.addClause(new VecInt(new int[] { 1, 2, 3 }));
        int[] model1 = solver.findModel();
        assertEquals(3, model1.length);
        int[] model2 = solver.modelWithInternalVariables();
        assertEquals(3, model2.length);
    }

    @Test
    public void testDeclaredVariables() throws ContradictionException,
            TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(10);
        assertEquals(10, solver.nVars());
        assertEquals(10, solver.realNumberOfVariables());
        solver.addClause(new VecInt(new int[] { 1, 2, 3 }));
        int[] model1 = solver.findModel();
        assertEquals(3, model1.length);
        int[] model2 = solver.modelWithInternalVariables();
        assertEquals(3, model2.length);
        for (int i = 0; i < 10; i++) {
            solver.nextFreeVarId(true);
        }
        assertEquals(10, solver.nVars());
        assertEquals(20, solver.realNumberOfVariables());
        model1 = solver.findModel();
        assertEquals(3, model1.length);
        System.out.println(new VecInt(model1));
        model2 = solver.modelWithInternalVariables();
        assertEquals(3, model2.length);
        int[] clause = { 14, 16, 19 };
        solver.addClause(new VecInt(clause));
        model1 = solver.findModel();
        assertEquals(3, model1.length);
        System.out.println(new VecInt(model1));
        model2 = solver.modelWithInternalVariables();
        assertEquals(6, model2.length);
    }

    @Test
    public void implicitDeclarationOfVariables() throws ContradictionException,
            TimeoutException {
        ISolver solver = SolverFactory.newDefault();
        assertEquals(0, solver.nVars());
        assertEquals(0, solver.realNumberOfVariables());
        solver.addClause(new VecInt(new int[] { 1, 2, 3 }));
        assertEquals(3, solver.nVars());
        assertEquals(3, solver.realNumberOfVariables());
        for (int i = 0; i < 10; i++) {
            solver.nextFreeVarId(true);
        }
        assertEquals(13, solver.nVars());
        assertEquals(13, solver.realNumberOfVariables());
        int[] model1 = solver.findModel();
        assertEquals(3, model1.length);
        int[] model2 = solver.modelWithInternalVariables();
        assertEquals(3, model2.length);
    }
}
