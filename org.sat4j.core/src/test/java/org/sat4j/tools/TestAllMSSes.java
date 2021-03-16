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

import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IGroupSolver;
import org.sat4j.specs.IVecInt;

public class TestAllMSSes {

    private AllMUSes allMUSes;
    private IGroupSolver solver;

    @Before
    public void setUp() throws Exception {
        this.allMUSes = new AllMUSes(true, SolverFactory.instance());
        this.solver = allMUSes.getSolverInstance();
    }

    @Test
    public void testSimpleCase() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();
        IVecInt c6 = new VecInt();
        IVecInt c7 = new VecInt();

        // a=1, b=2, c=3, d=4

        // a & c
        c1.push(1);
        c2.push(3);

        // b & c
        c3.push(2);
        c4.push(3);

        // b & d
        c5.push(2);
        c6.push(4);

        // -a | -b
        c7.push(-1).push(-2);

        this.solver.newVar(4);

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 1);
            this.solver.addClause(c3, 2);
            this.solver.addClause(c4, 2);
            this.solver.addClause(c5, 3);
            this.solver.addClause(c6, 3);
            this.solver.addClause(c7, 0);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            List<IVecInt> msses = allMUSes.getMssList();

            System.out
                    .println("MSS should be {b & c , b & d} and {a & c} i.e. {2,3} and {1}");
            System.out.println("MSS = " + msses);

            System.out
                    .println("MUS should be {a & c, b & c} and {a & c, b & d} i.e. {1,2} and {1,3}");
            System.out.println("MUS = " + muses);

            assertEquals(msses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }

    }

    @Test
    public void testSimpleCasePermut() {
        IVecInt c1 = new VecInt();
        IVecInt c2 = new VecInt();
        IVecInt c3 = new VecInt();
        IVecInt c4 = new VecInt();
        IVecInt c5 = new VecInt();
        IVecInt c6 = new VecInt();
        IVecInt c7 = new VecInt();

        // a=4, b=1, c=2, d=3

        // b & c
        c1.push(1);
        c2.push(2);

        // b & d
        c3.push(1);
        c4.push(3);

        // a & c
        c5.push(4);
        c6.push(2);

        // -a | -b
        c7.push(-4).push(-1);

        this.solver.newVar(4);

        try {
            this.solver.addClause(c1, 1);
            this.solver.addClause(c2, 1);
            this.solver.addClause(c3, 2);
            this.solver.addClause(c4, 2);
            this.solver.addClause(c5, 3);
            this.solver.addClause(c6, 3);
            this.solver.addClause(c7, 0);

            List<IVecInt> muses = allMUSes.computeAllMUSes();

            List<IVecInt> msses = allMUSes.getMssList();

            System.out
                    .println("MSS should be {b & c , b & d} and {a & c} i.e. {1,2} and {3}");
            System.out.println("MSS = " + msses);

            System.out
                    .println("MUS should be {a & c, b & c} and {a & c, b & d} i.e. {3,1} and {3,2}");
            System.out.println("MUS = " + muses);

            assertEquals(msses.size(), 2);

        } catch (ContradictionException e) {
            e.printStackTrace();
        }

    }

}
