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
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import org.junit.Test;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.TimeoutException;

public class BugSAT25 {

    @Test(expected = UnsupportedOperationException.class)
    public void testReaderFromInstanceReader() throws ParseFormatException,
            ContradictionException, IOException {
        String cnfString = "p cnf 3 4\n1 2 3 0\n-1 -2 0\n-1 -3 0\n-2 -3 0";
        InstanceReader reader = new InstanceReader(SolverFactory.newDefault());
        reader.parseInstance(new ByteArrayInputStream(cnfString.getBytes()));
        fail();
    }

    @Test
    public void testReaderFromDimacsReader() throws ParseFormatException,
            ContradictionException, IOException, TimeoutException {
        String cnfString = "p cnf 3 4\n1 2 3 0\n-1 -2 0\n-1 -3 0\n-2 -3 0";
        DimacsReader reader = new DimacsReader(SolverFactory.newDefault());
        IProblem problem = reader.parseInstance(new ByteArrayInputStream(
                cnfString.getBytes()));
        assertNotNull(problem);
        assertTrue(problem.isSatisfiable());
    }

    @Test
    public void testReaderFromLecteurDimacs() throws ParseFormatException,
            ContradictionException, IOException, TimeoutException {
        String cnfString = "p cnf 3 4\n1 2 3 0\n-1 -2 0\n-1 -3 0\n-2 -3 0";
        LecteurDimacs reader = new LecteurDimacs(SolverFactory.newDefault());
        IProblem problem = reader.parseInstance(new ByteArrayInputStream(
                cnfString.getBytes()));
        assertNotNull(problem);
        assertTrue(problem.isSatisfiable());
    }
}
