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
import static org.junit.Assert.assertNotNull;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.encoding.EncodingStrategy;
import org.sat4j.tools.encoding.Policy;

public class TestClausalCardinalitiesLadderEncoding {

    private ISolver solver;
    private Policy policy;
    private final static boolean MODE_DEBUG = false;

    @Before
    public void setUp() {
        this.policy = new Policy();
        this.policy.setAtMostOneEncoding(EncodingStrategy.LADDER);
        this.policy.setAtMostKEncoding(EncodingStrategy.LADDER);
        this.policy.setAtLeastOneEncoding(EncodingStrategy.LADDER);
        this.policy.setAtLeastKEncoding(EncodingStrategy.LADDER);
        this.policy.setExactlyOneEncoding(EncodingStrategy.LADDER);
        this.policy.setExactlyKEncoding(EncodingStrategy.LADDER);

        this.solver = new ClausalCardinalitiesDecorator<ISolver>(
                SolverFactory.newDefault(), policy);
    }

    @Test
    public void testAtMostOne() throws ContradictionException, TimeoutException {

        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addAtMost(clause, 1);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderAtMostOne");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderAtMostOne models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(6, cpt);
    }

    @Test
    public void testExactlyOne() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addExactly(clause, 1);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderExactlyOne");
            for (int i = 0; i < constr.size(); i++) {
                if (constr instanceof ConstrGroup)
                    System.out.println(((ConstrGroup) constr).getConstr(i));
                else
                    System.out.println(constr);
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderExactlyOne models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(5, cpt);
    }

    @Test
    public void testAtLeastOne() throws ContradictionException,
            TimeoutException {
        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addAtLeast(clause, 1);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderAtLeastOne");
            for (int i = 0; i < constr.size(); i++) {
                if (constr instanceof ConstrGroup)
                    System.out.println(((ConstrGroup) constr).getConstr(i));
                else
                    System.out.println(constr);
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderAtLeastOne models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(31, cpt);
    }

    @Test
    public void testAtMost2() throws ContradictionException, TimeoutException {

        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addAtMost(clause, 2);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderAtMost2");
            if (constr instanceof ConstrGroup) {
                for (int i = 0; i < constr.size(); i++) {

                    System.out.println(((ConstrGroup) constr).getConstr(i));

                }
            } else {
                System.out.println(constr);
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderAtMost2 models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(16, cpt);
    }

    @Test
    public void testAtLeast2() throws ContradictionException, TimeoutException {

        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addAtLeast(clause, 2);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderAtLeast2");
            if (constr instanceof ConstrGroup) {
                for (int i = 0; i < constr.size(); i++) {

                    System.out.println(((ConstrGroup) constr).getConstr(i));

                }
            } else {
                System.out.println(constr);
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderAtLeast2 models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(26, cpt);
    }

    @Test
    public void testExactly2() throws ContradictionException, TimeoutException {

        this.solver.newVar(5);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);

        IConstr constr = this.solver.addExactly(clause, 2);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderExactly2");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderExactly2 models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(10, cpt);
    }

    @Test
    public void testAtMostOneWith8Vars() throws ContradictionException,
            TimeoutException {

        this.solver.newVar(8);

        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5).push(6).push(7).push(8);

        IConstr constr = this.solver.addAtMost(clause, 1);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testLadderAtMostOneWith8Vars");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testLadderAtMostOneWith8Vars models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(9, cpt);
    }

    @Test
    public void testExactly4With11Vars() throws ContradictionException,
            TimeoutException {

        int nVar = 11;
        this.solver.newVar(nVar);

        int degree = 4;

        IVecInt clause = new VecInt();
        for (int i = 1; i <= nVar; i++) {
            clause.push(i);
        }

        IConstr constr = this.solver.addExactly(clause, degree);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testExactly4With11Vars");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testExactly4With11Vars models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(330, cpt);
    }

    @Test
    public void testAtMost4With11Vars() throws ContradictionException,
            TimeoutException {

        int nVar = 11;
        this.solver.newVar(nVar);

        int degree = 4;

        IVecInt clause = new VecInt();
        for (int i = 1; i <= nVar; i++) {
            clause.push(i);
        }

        IConstr constr = this.solver.addAtMost(clause, degree);
        assertNotNull(constr);

        if (MODE_DEBUG) {
            System.out.println();
            System.out.println("testAtMost4With11Vars");
            if (constr instanceof ConstrGroup) {
                for (int i = 0; i < constr.size(); i++) {
                    System.out.println(((ConstrGroup) constr).getConstr(i));
                }
            } else {
                System.out.println(constr);
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG)
            System.out.println("testAtMost4With11Vars models");
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG)
                System.out.println(new VecInt(model));
            cpt++;
        }
        assertEquals(562, cpt);
    }
}
