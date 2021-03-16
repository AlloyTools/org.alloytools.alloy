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

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

@RunWith(Parameterized.class)
public class BugSAT34 {

    ISolver system;
    String solvername;

    public BugSAT34(ISolver system, String solvername) {
        this.system = system;
        this.solvername = solvername;
    }

    @Parameters
    public static Collection<Object[]> generateSolvers() {
        Collection<Object[]> solvers = new ArrayList<Object[]>();
        for (String name : SolverFactory.instance().solverNames()) {
            if (!"DimacsOutput".equals(name) && !"Statistics".equals(name)) {
                solvers.add(new Object[] {
                        SolverFactory.instance().createSolverByName(name),
                        name });
            }
        }
        return solvers;
    }

    @Test
    public void testUnitClause() {
        this.system.newVar(3);
        try {
            // x_1 v x_2 <=> x_3
            IConstr nonunit;
            nonunit = this.system.addClause(new VecInt(new int[] { 1, 2, -3 }));
            assertNotNull(nonunit);
            nonunit = this.system.addClause(new VecInt(new int[] { -1, 3 }));
            assertNotNull(nonunit);
            nonunit = this.system.addClause(new VecInt(new int[] { -2, 3 }));
            assertNotNull(nonunit);
            // not both true
            this.system.addClause(new VecInt(new int[] { -1, -2 }));
            // x2 is true
            IConstr unit = this.system.addClause(new VecInt(new int[] { 2 }));
            assertNotNull(this.solvername + " has unit clause problem", unit);
            // x3 is true
            IConstr cl = this.system.addAtLeast(new VecInt(new int[] { 3 }), 1);
            assertNotNull(this.solvername + " has unit clause problem", cl);
            int[] model = this.system.findModel();
            assertNotNull(this.solvername + " has a model problem", model);
            this.system.removeConstr(cl);
            // x3 is true
            cl = this.system.addAtLeast(new VecInt(new int[] { 3 }), 1);
            assertNotNull(this.solvername + " has unit clause problem", cl);
            // x1 is true
            // so here x1, x2 and x3 is true
            IConstr r = this.system.addClause(new VecInt(new int[] { 1 }));
            assertNotNull(r);
            assertNotNull(this.solvername + " has unit clause problem", r);
            model = this.system.findModel();
            assertNull(this.solvername + " has a model problem", model);
        } catch (ContradictionException e) {
        } catch (TimeoutException e) {
        }
        ;
    }

}
