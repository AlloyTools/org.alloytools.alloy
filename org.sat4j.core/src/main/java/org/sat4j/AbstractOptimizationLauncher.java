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

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.TimeoutException;

/**
 * This class is intended to be used by launchers to solve optimization
 * problems, i.e. problems for which a loop is needed to find the optimal
 * solution.
 * 
 * This class is no longer used since 2.3.3
 * 
 * @see ILauncherMode
 * 
 * @author leberre
 * 
 */
@Deprecated
public abstract class AbstractOptimizationLauncher extends AbstractLauncher {

    /**
	 * 
	 */
    private static final long serialVersionUID = 1L;

    private static final String CURRENT_OPTIMUM_VALUE_PREFIX = "o "; //$NON-NLS-1$

    private boolean incomplete = false;

    private boolean displaySolutionLine = true;

    @Override
    protected void setIncomplete(boolean value) {
        this.incomplete = value;
    }

    @Override
    protected void setDisplaySolutionLine(boolean value) {
        this.displaySolutionLine = value;
    }

    @Override
    protected void displayResult() {
        displayAnswer();

        log("Total wall clock time (in seconds): " //$NON-NLS-1$
                + (System.currentTimeMillis() - getBeginTime()) / 1000.0);
    }

    protected void displayAnswer() {
        if (this.solver == null) {
            return;
        }
        System.out.flush();
        PrintWriter out = getLogWriter();
        out.flush();
        this.solver.printStat(out, COMMENT_PREFIX);
        this.solver.printInfos(out, COMMENT_PREFIX);
        ExitCode exitCode = getExitCode();
        out.println(ILauncherMode.ANSWER_PREFIX + exitCode);
        if (exitCode == ExitCode.SATISFIABLE
                || exitCode == ExitCode.OPTIMUM_FOUND || this.incomplete
                && exitCode == ExitCode.UPPER_BOUND) {
            if (this.displaySolutionLine) {
                out.print(ILauncherMode.SOLUTION_PREFIX);
                getReader().decode(this.solver.model(), out);
                out.println();
            }
            IOptimizationProblem optproblem = (IOptimizationProblem) this.solver;
            if (!optproblem.hasNoObjectiveFunction()) {
                log("objective function=" + optproblem.getObjectiveValue()); //$NON-NLS-1$
            }
        }
    }

    @Override
    protected void solve(IProblem problem) throws TimeoutException {
        boolean isSatisfiable = false;

        IOptimizationProblem optproblem = (IOptimizationProblem) problem;

        try {
            while (optproblem.admitABetterSolution()) {
                if (!isSatisfiable) {
                    if (optproblem.nonOptimalMeansSatisfiable()) {
                        setExitCode(ExitCode.SATISFIABLE);
                        if (optproblem.hasNoObjectiveFunction()) {
                            return;
                        }
                        log("SATISFIABLE"); //$NON-NLS-1$
                    } else if (this.incomplete) {
                        setExitCode(ExitCode.UPPER_BOUND);
                    }
                    isSatisfiable = true;
                    log("OPTIMIZING..."); //$NON-NLS-1$
                }
                log("Got one! Elapsed wall clock time (in seconds):" //$NON-NLS-1$
                        + (System.currentTimeMillis() - getBeginTime())
                        / 1000.0);
                getLogWriter().println(
                        CURRENT_OPTIMUM_VALUE_PREFIX
                                + optproblem.getObjectiveValue());
                optproblem.discardCurrentSolution();
            }
            if (isSatisfiable) {
                setExitCode(ExitCode.OPTIMUM_FOUND);
            } else {
                setExitCode(ExitCode.UNSATISFIABLE);
            }
        } catch (ContradictionException ex) {
            assert isSatisfiable;
            setExitCode(ExitCode.OPTIMUM_FOUND);
        }
    }

}
