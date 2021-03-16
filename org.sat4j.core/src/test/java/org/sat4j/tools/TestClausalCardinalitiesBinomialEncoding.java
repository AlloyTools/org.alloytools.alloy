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

public class TestClausalCardinalitiesBinomialEncoding {

    private ISolver solver;
    private Policy policy;
    private final static boolean MODE_DEBUG = false;

    @Before
    public void setUp() {
        this.policy = new Policy();
        this.policy.setAtMostOneEncoding(EncodingStrategy.BINOMIAL);
        this.policy.setAtMostKEncoding(EncodingStrategy.BINOMIAL);
        this.policy.setAtLeastOneEncoding(EncodingStrategy.BINOMIAL);
        this.policy.setAtLeastKEncoding(EncodingStrategy.BINOMIAL);
        this.policy.setExactlyOneEncoding(EncodingStrategy.BINOMIAL);
        this.policy.setExactlyKEncoding(EncodingStrategy.BINOMIAL);

        this.solver = new ClausalCardinalitiesDecorator<ISolver>(
                SolverFactory.newDefault(), this.policy);
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
            System.out.println("testBinomialAtMostOne");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialAtMostOne models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
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
            System.out.println("testBinomialExactlyOne");
            for (int i = 0; i < constr.size(); i++) {
                if (constr instanceof ConstrGroup) {
                    System.out.println(((ConstrGroup) constr).getConstr(i));
                } else {
                    System.out.println(constr);
                }
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialExactlyOne models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
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
            System.out.println("testBinomialAtLeastOne");
            for (int i = 0; i < constr.size(); i++) {
                if (constr instanceof ConstrGroup) {
                    System.out.println(((ConstrGroup) constr).getConstr(i));
                } else {
                    System.out.println(constr);
                }
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialAtLeastOne models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
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
            System.out.println("testBinomialAtMost2");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialAtMost2 models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
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
            System.out.println("testBinomialAtLeast2");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialAtLeast2 models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
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
            System.out.println("testBinomialExactly2");
            for (int i = 0; i < constr.size(); i++) {
                System.out.println(((ConstrGroup) constr).getConstr(i));
            }
        }

        ModelIterator iterator = new ModelIterator(this.solver);
        int[] model = null;
        int cpt = 0;

        if (MODE_DEBUG) {
            System.out.println("testBinomialExactly2 models");
        }
        while (iterator.isSatisfiable()) {
            model = iterator.model();
            assertNotNull(model);
            if (MODE_DEBUG) {
                System.out.println(new VecInt(model));
            }
            cpt++;
        }
        assertEquals(10, cpt);
    }

    // @Test
    // public void testSimpleCardCase() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(5);
    //
    // boolean debug = false;
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5);
    //
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    //
    // IConstr constr2 = this.solver.addAtMost(clause, 1);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    //
    // System.out.println("testSimpleCardCase models AMO + clause");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(5, cpt);
    //
    // }
    //
    // @Test
    // public void testSimpleCardCase2Power() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(4);
    //
    // boolean debug = false;
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4);
    //
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    //
    // IConstr constr2 = this.solver.addAtMost(clause, 1);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    //
    // System.out.println("testSimpleCardCase2Power models AMO + clause");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(4, cpt);
    //
    // }
    //
    // @Test
    // public void testSimpleCardCaseAMO() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(5);
    //
    // boolean debug = false;
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5);
    //
    // IConstr constr2 = this.solver.addAtMost(clause, 1);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // System.out.println("Constraintes AMO");
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    // System.out.println("testSimpleCardCase models AMO");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(6, cpt);
    //
    // }
    //
    // @Test
    // public void testSimpleCardCaseAMOWith8Variables()
    // throws ContradictionException, TimeoutException {
    // this.solver.newVar(8);
    //
    // boolean debug = false;
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5).push(6).push(7).push(8);
    //
    // IConstr constr2 = this.solver.addAtMost(clause, 1);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // System.out.println("Constraintes AMO 8 variables");
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // System.out.println("testSimpleCardCase models AMO 8 variables");
    // int cpt = 0;
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(9, cpt);
    //
    // }
    //
    // @Test
    // public void testSimpleCardCaseEO() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(5);
    //
    // boolean debug = false;
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5);
    //
    // IConstr constr = this.solver.addExactly(clause, 1);
    // assertNotNull(constr);
    //
    // assertEquals(2, constr.size());
    //
    // if (debug) {
    // System.out.println("Constraintes EO");
    // for (int i = 0; i < constr.size(); i++) {
    // System.out.println(((ConstrGroup) constr).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    // System.out.println("testSimpleCardCase models EO");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(5, cpt);
    //
    // }
    //
    // @Test
    // public void testSimpleCardCaseFor2() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(5);
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5);
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    // IConstr constr2 = this.solver.addAtMost(clause, 2);
    // assertNotNull(constr2);
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    // System.out
    // .println("testSimpleCardCaseFor2 - AMO + clauses - 5 variables");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(15, cpt);
    // }
    //
    // @Test
    // public void testSimpleCardCaseFor2With7Variables()
    // throws ContradictionException, TimeoutException {
    //
    // boolean debug = false;
    //
    // int nbVar = 7;
    // this.solver.newVar(nbVar);
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5).push(6).push(7);
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    // IConstr constr2 = this.solver.addAtMost(clause, 2);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // System.out
    // .println("Constraints Simple card case for 2 with 7 variables");
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    // System.out
    // .println("testSimpleCardCaseFor2With7Variables models AMO + clause - 7 variables");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(28, cpt);
    // }
    //
    // @Test
    // public void testSimpleCardCaseFor2With8Variables()
    // throws ContradictionException, TimeoutException {
    //
    // boolean debug = false;
    //
    // int nbVar = 8;
    // this.solver.newVar(nbVar);
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5).push(6).push(7).push(8);
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    // IConstr constr2 = this.solver.addAtMost(clause, 2);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // System.out
    // .println("Constraints Simple card case for 2 with 8 variables");
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // int cpt = 0;
    // System.out
    // .println("testSimpleCardCaseFor2With8Variables models AMO + clause - 8 variables");
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(36, cpt);
    // }
    //
    // @Test
    // public void testSimpleCardCaseFor4With11Variables()
    // throws ContradictionException, TimeoutException {
    //
    // boolean debug = false;
    //
    // int nbVar = 11;
    // this.solver.newVar(nbVar);
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5).push(6).push(7).push(8)
    // .push(9).push(10).push(11);
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    // IConstr constr2 = this.solver.addAtMost(clause, 4);
    // assertNotNull(constr2);
    //
    // if (debug) {
    // System.out
    // .println("Constraints Simple card case for 4 with 11 variables");
    // for (int i = 0; i < constr2.size(); i++) {
    // System.out.println(((ConstrGroup) constr2).getConstr(i));
    // }
    // }
    //
    // ModelIterator iterator = new ModelIterator(this.solver);
    // int[] model = null;
    // System.out
    // .println("testSimpleCardCaseFor4With11Variables models AMO + clause - 11 variables");
    // int cpt = 0;
    // while (iterator.isSatisfiable()) {
    // model = iterator.model();
    // assertNotNull(model);
    // System.out.println(new VecInt(model));
    // cpt++;
    // }
    // assertEquals(561, cpt);
    // }
    //
    // @Test
    // public void testSimpleCardCaseForUnsat() throws ContradictionException,
    // TimeoutException {
    // this.solver.newVar(5);
    // IVecInt clause = new VecInt();
    // clause.push(1).push(2).push(3).push(4).push(5);
    // IConstr constr1 = this.solver.addClause(clause);
    // assertNotNull(constr1);
    // IConstr constr2 = this.solver.addAtMost(clause, 0);
    // assertNotNull(constr2);
    // assertFalse(this.solver.isSatisfiable());
    // }

    // @Test
    // public void testName() {
    // System.out.println(this.solver.toString());
    // }
}
