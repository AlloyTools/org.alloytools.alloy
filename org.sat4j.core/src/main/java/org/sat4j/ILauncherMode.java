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

import java.io.PrintWriter;

import org.sat4j.reader.Reader;
import org.sat4j.specs.ILogAble;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.tools.SolutionFoundListener;

/**
 * Allow to change the behavior of the launcher (either decision or optimization
 * mode)
 * 
 * @since 2.3.3
 * @author sroussel
 * 
 */
public interface ILauncherMode extends SolutionFoundListener {

    String SOLUTION_PREFIX = "v "; //$NON-NLS-1$

    String ANSWER_PREFIX = "s "; //$NON-NLS-1$

    String CURRENT_OPTIMUM_VALUE_PREFIX = "o ";

    /**
     * Output of the launcher when the solver stops
     * 
     * @param solver
     *            the solver that is launched by the launcher
     * @param problem
     *            the problem that is solved
     * @param logger
     *            the element that is able to log the result
     * @param out
     *            the printwriter to associate to the solver
     * @param reader
     *            the problem reader
     * @param beginTime
     *            the time at which the solver was launched
     * @param displaySolutionLine
     *            indicates whether the solution line shound be displayed or not
     *            (not recommended for large solutions)
     */
    void displayResult(ISolver solver, IProblem problem, ILogAble logger,
            PrintWriter out, Reader reader, long beginTime,
            boolean displaySolutionLine);

    /**
     * Main solver call: one call for a decision problem, a loop for an
     * optimization problem.
     * 
     * @param problem
     *            the problem to solve
     * @param reader
     *            the reader that provided the problem object
     * @param logger
     *            the element that is able to log the result
     * @param out
     *            the printwriter to associate to the solver
     * @param beginTime
     *            the time at which the solver starts
     */
    void solve(IProblem problem, Reader reader, ILogAble logger,
            PrintWriter out, long beginTime);

    /**
     * Allows the launcher to specifically return an upper bound of the optimal
     * solution in case of a time out (for maxsat competitions for instance).
     * 
     * @param isIncomplete
     *            true if the solver should return the best solution found so
     *            far.
     */
    void setIncomplete(boolean isIncomplete);

    /**
     * Allow the launcher to get the current status of the problem: SAT, UNSAT,
     * UPPER_BOUND, etc.
     * 
     * @return the status of the problem.
     */
    ExitCode getCurrentExitCode();

    /**
     * Allow to set a specific exit code to the launcher (in case of trivial
     * unsatisfiability for instance).
     * 
     * @param exitCode
     *            the status of the problem to solve
     */
    void setExitCode(ExitCode exitCode);

    /**
     * The launcher is in decision mode: the answer is either SAT, UNSAT or
     * UNKNOWN
     */
    ILauncherMode DECISION = new DecisionMode();

    /**
     * The launcher is in optimization mode: the answer is either SAT,
     * UPPER_BOUND, OPTIMUM_FOUND, UNSAT or UNKNOWN. Using the incomplete
     * property, the solver returns an upper bound of the optimal solution when
     * a time out occurs.
     */
    ILauncherMode OPTIMIZATION = new OptimizationMode();

}
