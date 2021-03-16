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

import org.sat4j.annotations.Feature;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ILogAble;
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.LexicoDecorator;

/**
 * Behavior of the solver when an optimal solution is needed.
 * 
 * @author leberre
 * 
 */
@Feature("solutionlistener")
final class OptimizationMode implements ILauncherMode {
    private int nbSolutions;
    private ExitCode exitCode = ExitCode.UNKNOWN;
    private boolean isIncomplete = false;
    private PrintWriter out;
    private long beginTime;
    private IOptimizationProblem problem;

    public void setIncomplete(boolean isIncomplete) {
        this.isIncomplete = isIncomplete;
    }

    public void displayResult(ISolver solver, IProblem problem, ILogAble logger,
            PrintWriter out, Reader reader, long beginTime,
            boolean displaySolutionLine) {
        if (solver == null) {
            return;
        }
        System.out.flush();
        out.flush();
        solver.printStat(out);
        out.println(ANSWER_PREFIX + exitCode);
        if (exitCode == ExitCode.SATISFIABLE
                || exitCode == ExitCode.OPTIMUM_FOUND
                || isIncomplete && exitCode == ExitCode.UPPER_BOUND) {
            assert this.nbSolutions > 0;
            logger.log("Found " + this.nbSolutions + " solution(s)");

            if (displaySolutionLine) {
                out.print(SOLUTION_PREFIX);
                reader.decode(problem.model(), out);
                out.println();
            }
            IOptimizationProblem optproblem = (IOptimizationProblem) problem;
            if (!optproblem.hasNoObjectiveFunction()) {
                String objvalue;
                if (optproblem instanceof LexicoDecorator<?>) {
                    IVec<Number> values = new Vec<Number>();
                    LexicoDecorator<?> lexico = (LexicoDecorator<?>) optproblem;
                    for (int i = 0; i < lexico.numberOfCriteria(); i++) {
                        values.push(lexico.getObjectiveValue(i));
                    }
                    objvalue = values.toString();

                } else {
                    objvalue = optproblem.getObjectiveValue().toString();
                }
                logger.log("objective function=" + objvalue); //$NON-NLS-1$
            }
        }

        logger.log("Total wall clock time (in seconds): " //$NON-NLS-1$
                + (System.currentTimeMillis() - beginTime) / 1000.0);
        out.flush();
    }

    public void solve(IProblem problem, Reader reader, ILogAble logger,
            PrintWriter out, long beginTime) {
        boolean isSatisfiable = false;
        this.nbSolutions = 0;
        IOptimizationProblem optproblem = (IOptimizationProblem) problem;
        exitCode = ExitCode.UNKNOWN;

        this.out = out;
        this.beginTime = beginTime;
        this.problem = optproblem;

        try {
            while (optproblem.admitABetterSolution()) {
                ++this.nbSolutions;
                if (!isSatisfiable) {
                    if (optproblem.nonOptimalMeansSatisfiable()) {
                        logger.log("SATISFIABLE");
                        exitCode = ExitCode.SATISFIABLE;
                        if (optproblem.hasNoObjectiveFunction()) {
                            return;
                        }
                    } else if (isIncomplete) {
                        exitCode = ExitCode.UPPER_BOUND;
                    }
                    isSatisfiable = true;
                    logger.log("OPTIMIZING..."); //$NON-NLS-1$
                }
                logger.log("Got one! Elapsed wall clock time (in seconds):" //$NON-NLS-1$
                        + (System.currentTimeMillis() - beginTime) / 1000.0);
                out.println(CURRENT_OPTIMUM_VALUE_PREFIX
                        + optproblem.getObjectiveValue());
                optproblem.discardCurrentSolution();
            }
            if (isSatisfiable) {
                exitCode = ExitCode.OPTIMUM_FOUND;
            } else {
                exitCode = ExitCode.UNSATISFIABLE;
            }
        } catch (ContradictionException ex) {
            assert isSatisfiable;
            exitCode = ExitCode.OPTIMUM_FOUND;
        } catch (TimeoutException e) {
            logger.log("timeout");
        }

    }

    public ExitCode getCurrentExitCode() {
        return exitCode;
    }

    public void onSolutionFound(int[] solution) {
        this.nbSolutions++;
        // this.exitCode = ExitCode.SATISFIABLE;
        this.out.printf("c Found solution #%d  (%.2f)s%n", nbSolutions,
                (System.currentTimeMillis() - beginTime) / 1000.0);
        this.out.println("c Value of objective function : "
                + problem.getObjectiveValue());
        if (System.getProperty("printallmodels") != null) {
            this.out.println(
                    new VecInt(solution).toString().replace(",", " ") + " 0");
        }
    }

    public void onSolutionFound(IVecInt solution) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void onUnsatTermination() {
        // do nothing
    }

    public void setExitCode(ExitCode exitCode) {
        this.exitCode = exitCode;
    }
}