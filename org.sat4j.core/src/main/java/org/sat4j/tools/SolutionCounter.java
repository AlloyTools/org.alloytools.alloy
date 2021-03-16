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

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Another solver decorator that counts the number of solutions.
 * 
 * Note that this approach is quite naive so do not expect it to work on large
 * examples. The number of solutions will be wrong if the SAT solver does not
 * provide a complete assignment.
 * 
 * The class is expected to be used that way:
 * 
 * <pre>
 * SolutionCounter counter = new SolverCounter(SolverFactory.newDefault());
 * try {
 *     int nbSol = counter.countSolutions();
 *     // the exact number of solutions is nbSol
 *     ...
 *  } catch (TimeoutException te) {
 *     int lowerBound = counter.lowerBound();
 *     // the solver found lowerBound solutions so far.
 *     ...
 *  }
 * </pre>
 * 
 * @author leberre
 * 
 */
@Feature("solver")
public class SolutionCounter extends SolverDecorator<ISolver> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private int lowerBound;

    public SolutionCounter(ISolver solver) {
        super(solver);
    }

    /**
     * Get the number of solutions found before the timeout occurs.
     * 
     * @return the number of solutions found so far.
     * @since 2.1
     */
    public int lowerBound() {
        return this.lowerBound;
    }

    /**
     * Naive approach to count the solutions available in a boolean formula:
     * each time a solution is found, a new clause is added to prevent it to be
     * found again.
     * 
     * @return the number of solution found.
     * @throws TimeoutException
     *             if the timeout given to the solver is reached.
     */
    public long countSolutions() throws TimeoutException {
        this.lowerBound = 0;
        boolean trivialfalsity = false;

        while (!trivialfalsity && isSatisfiable(true)) {
            this.lowerBound++;
            int[] last = model();
            IVecInt clause = new VecInt(last.length);
            for (int q : last) {
                clause.push(-q);
            }
            try {
                addClause(clause);
            } catch (ContradictionException e) {
                trivialfalsity = true;
            }
        }
        return this.lowerBound;
    }
}
