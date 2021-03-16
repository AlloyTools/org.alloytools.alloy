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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.opt.MaxSatDecorator;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.OptToSatAdapter;

public class Bug275101 {

    @Test
    public void testMaxSAtIteratorIfSat() throws ContradictionException,
            TimeoutException {
        ISolver solver = new ModelIterator(new OptToSatAdapter(
                new MaxSatDecorator(SolverFactory.newDefault())));
        solver.newVar(3);
        IVecInt literals = new VecInt();
        literals.push(-1).push(-2).push(3);
        solver.addClause(literals);
        literals.clear();
        literals.push(-1).push(2);
        solver.addClause(literals);
        literals.clear();
        literals.push(-1).push(-3);
        solver.addClause(literals);
        literals.clear();
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertTrue(solver.isSatisfiable());
        assertEquals(3, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2)
                + solver.model(3));
        assertFalse(solver.isSatisfiable());
    }

    @Test
    public void testMaxSAtIterator() throws ContradictionException,
            TimeoutException {
        ISolver solver = new ModelIterator(new OptToSatAdapter(
                new MaxSatDecorator(SolverFactory.newDefault())));
        solver.newVar(2);
        IVecInt literals = new VecInt();
        literals.push(-1).push(-2);
        solver.addClause(literals);
        literals.clear();
        literals.push(-1).push(2);
        solver.addClause(literals);
        literals.clear();
        literals.push(1).push(-2);
        solver.addClause(literals);
        literals.clear();
        literals.push(1).push(2);
        solver.addClause(literals);
        assertTrue(solver.isSatisfiable());
        assertEquals(2, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2));
        assertTrue(solver.isSatisfiable());
        assertEquals(2, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2));
        assertTrue(solver.isSatisfiable());
        assertEquals(2, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2));
        assertTrue(solver.isSatisfiable());
        assertEquals(2, solver.model().length);
        System.out.println("" + solver.model(1) + solver.model(2));
        assertFalse(solver.isSatisfiable());
    }
}
