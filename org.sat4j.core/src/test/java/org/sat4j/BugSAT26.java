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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

public class BugSAT26 {
    private Xplain<ISolver> xplain;

    @Before
    public void setUp() throws FileNotFoundException, ParseFormatException,
            IOException, ContradictionException {
        this.xplain = new Xplain<ISolver>(SolverFactory.newDefault());
        this.xplain.setTimeout(3600); // 1 hour timeout
        Reader reader = new DimacsReader(this.xplain);
        String dimacs = "src/test/testfiles/eb42.dimacs";
        reader.parseInstance(dimacs);
    }

    @Test
    public void testConsecutiveCallToSolver()
            throws ContradictionException, TimeoutException {
        assertTrue(this.xplain.isSatisfiable());
        int i = 0;
        while (i < 5) {
            VecInt assumption = new VecInt();
            assumption.push(1187);
            IConstr constr = this.xplain.addClause(assumption);
            assertFalse(this.xplain.isSatisfiable());
            this.xplain.removeConstr(constr);
            assertTrue(this.xplain.isSatisfiable());
            i++;
        }
    }
}
