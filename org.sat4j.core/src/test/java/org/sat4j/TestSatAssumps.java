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

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class TestSatAssumps {
    @Test
    public void testIterativeAssumptionCallsWithSet()
            throws FileNotFoundException, ParseFormatException, IOException,
            ContradictionException, TimeoutException {
        ISolver satSolver = SolverFactory.newDefault();
        Reader reader = new LecteurDimacs(satSolver);
        IProblem p = reader.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

        List<Integer> vars = new ArrayList<Integer>();
        for (int i = 1; i <= p.nVars(); i++) {
            vars.add(-i);
            vars.add(i);
        }

        Set<Integer> sol = new HashSet<Integer>();

        for (int i = 0; i < vars.size(); i++) {
            ISolver satSolverOracle = SolverFactory.newDefault();
            Reader readerOracle = new LecteurDimacs(satSolverOracle);
            readerOracle.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

            int varnr = vars.get(i);

            int assumpsArray[] = new int[sol.size() + 1];
            int c = 0;
            for (int a : sol) {
                assumpsArray[c] = a;
                c++;
            }
            assumpsArray[assumpsArray.length - 1] = varnr;
            IVecInt assumps = new VecInt(assumpsArray);
            // Check
            if (satSolver.isSatisfiable(assumps)) {
                sol.add(varnr);
            }

            assertEquals(satSolverOracle.isSatisfiable(assumps),
                    satSolver.isSatisfiable(assumps));
        }
    }

    @Test
    public void testIterativeAssumptionCallsWithList()
            throws FileNotFoundException, ParseFormatException, IOException,
            ContradictionException, TimeoutException {
        ISolver satSolver = SolverFactory.newDefault();
        Reader reader = new LecteurDimacs(satSolver);
        IProblem p = reader.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

        List<Integer> vars = new ArrayList<Integer>();
        for (int i = 1; i <= p.nVars(); i++) {
            vars.add(-i);
            vars.add(i);
        }

        List<Integer> sol = new ArrayList<Integer>();

        for (int i = 0; i < vars.size(); i++) {
            ISolver satSolverOracle = SolverFactory.newDefault();
            Reader readerOracle = new LecteurDimacs(satSolverOracle);
            readerOracle.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

            int varnr = vars.get(i);

            int assumpsArray[] = new int[sol.size() + 1];
            int c = 0;
            for (int a : sol) {
                assumpsArray[c] = a;
                c++;
            }
            assumpsArray[assumpsArray.length - 1] = varnr;
            IVecInt assumps = new VecInt(assumpsArray);

            // Check
            if (satSolver.isSatisfiable(assumps)) {
                sol.add(varnr);
            }

            assertEquals(satSolverOracle.isSatisfiable(assumps),
                    satSolver.isSatisfiable(assumps));
        }
    }

    @Test
    public void testIterativeCorrectWay() throws FileNotFoundException,
            ParseFormatException, IOException, ContradictionException,
            TimeoutException {
        ISolver satSolver = SolverFactory.newDefault();
        Reader reader = new LecteurDimacs(satSolver);
        IProblem p = reader.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

        Set<Integer> sol = new HashSet<Integer>();

        for (int i = 1; i <= p.nVars(); i++) {
            ISolver satSolverOracle = SolverFactory.newDefault();
            Reader readerOracle = new LecteurDimacs(satSolverOracle);
            readerOracle.parseInstance("src/test/testfiles/Eshop-fm.dimacs");

            int assumpsArray[] = new int[sol.size() + 1];
            int c = 0;
            for (int a : sol) {
                assumpsArray[c] = a;
                c++;
            }
            assumpsArray[assumpsArray.length - 1] = -i;
            IVecInt assumps = new VecInt(assumpsArray);

            // Check
            assertEquals(satSolverOracle.isSatisfiable(assumps),
                    satSolver.isSatisfiable(assumps));
            if (satSolver.isSatisfiable(assumps)) {
                sol.add(-i);
                continue;
            }
            assumpsArray[assumpsArray.length - 1] = i;
            satSolverOracle = SolverFactory.newDefault();
            readerOracle = new LecteurDimacs(satSolverOracle);
            readerOracle.parseInstance("src/test/testfiles/Eshop-fm.dimacs");
            assertEquals(satSolverOracle.isSatisfiable(assumps),
                    satSolver.isSatisfiable(assumps));
            if (satSolver.isSatisfiable(assumps)) {
                sol.add(i);
            }
        }
    }
}
