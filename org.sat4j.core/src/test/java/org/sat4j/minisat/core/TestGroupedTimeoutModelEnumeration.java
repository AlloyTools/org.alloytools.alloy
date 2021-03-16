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

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

public class TestGroupedTimeoutModelEnumeration {

    private ISolver solver;

    @Before
    public void setUp() throws ContradictionException {
        this.solver = new ModelIterator(SolverFactory.newDefault());
        IVecInt clause = new VecInt();
        for (int i = 1; i <= 15; i++) {
            clause.push(-i);
        }
        this.solver.addClause(clause);
    }

    @Test(expected = TimeoutException.class, timeout = 6000)
    public void testTimeoutOnSeconds() throws TimeoutException {
        this.solver.setTimeout(2);
        while (this.solver.isSatisfiable()) {
            this.solver.model(); // needed to discard that solution
        }
    }

    @Test(expected = TimeoutException.class, timeout = 6000)
    public void testTimeoutOnMilliSeconds() throws TimeoutException {
        this.solver.setTimeoutMs(2000);
        while (this.solver.isSatisfiable()) {
            this.solver.model(); // needed to discard that solution
        }
    }

    // the new implementation of the model iterator does not generate any
    // conflict during the enumeration ...
    @Ignore
    public void testTimeoutOnConflicts() throws TimeoutException {
        this.solver.setTimeoutOnConflicts(100);
        int i = 1;
        while (this.solver.isSatisfiable()) {
            System.out
                    .println(this.solver.createBlockingClauseForCurrentModel());
            this.solver.model(); // needed to discard that solution

        }
        this.solver.printStat(System.out, ">");
    }
}
