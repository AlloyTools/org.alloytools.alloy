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
import org.sat4j.reader.Reader;
import org.sat4j.specs.AssignmentOrigin;
import org.sat4j.specs.ILogAble;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.Backbone;

/**
 * Behavior of the solver when one single solution is needed.
 * 
 * @author leberre
 * 
 */
@Feature("solutionlistener")
final class DecisionMode implements ILauncherMode {
    private ExitCode exitCode = ExitCode.UNKNOWN;
    private int nbSolutionFound;
    private PrintWriter out;
    private long beginTime;
    private Reader reader;
    private ISolver solver;

    public void displayResult(ISolver solver, IProblem problem, ILogAble logger,
            PrintWriter out, Reader reader, long beginTime,
            boolean displaySolutionLine) {
        if (solver != null) {
            out.flush();
            double wallclocktime = (System.currentTimeMillis() - beginTime)
                    / 1000.0;
            solver.printStat(out);
            out.println(ANSWER_PREFIX + exitCode);
            if (exitCode != ExitCode.UNKNOWN
                    && exitCode != ExitCode.UNSATISFIABLE) {
                int[] model = problem.model();
                if (System.getProperty("prime") != null) {
                    int initiallength = model.length;
                    logger.log("returning a prime implicant ...");
                    long beginpi = System.currentTimeMillis();
                    model = solver.primeImplicant();
                    long endpi = System.currentTimeMillis();
                    logger.log("removed " + (initiallength - model.length)
                            + " literals");
                    logger.log("pi computation time: " + (endpi - beginpi)
                            + " ms");
                }
                if (System.getProperty("backbone") != null) {
                    logger.log("computing the backbone of the formula ...");
                    long beginpi = System.currentTimeMillis();
                    model = solver.primeImplicant();
                    try {
                        IVecInt backbone = Backbone.instance().compute(solver,
                                model);
                        long endpi = System.currentTimeMillis();
                        out.print(solver.getLogPrefix());
                        reader.decode(backbone.toArray(), out);
                        out.println();
                        logger.log("backbone computation time: "
                                + (endpi - beginpi) + " ms");
                    } catch (TimeoutException e) {
                        logger.log("timeout, cannot compute the backbone.");
                    }

                }
                if (nbSolutionFound >= 1) {
                    logger.log("Found " + nbSolutionFound + " solution(s)");
                } else {
                    printSolution(solver, out, reader, model);
                }
            }
            logger.log("Total wall clock time (in seconds) : " + wallclocktime); //$NON-NLS-1$
        }
    }

    private void printSolution(ISolver solver, PrintWriter out, Reader reader,
            int[] model) {
        out.print(SOLUTION_PREFIX);
        if (System.getProperty("color") == null) {
            reader.decode(model, out);
            out.println();
        } else {
            int[] stats = new int[AssignmentOrigin.values().length];
            AssignmentOrigin origin;
            for (int p : model) {
                origin = solver.getOriginInModel(p);
                out.print(origin.getColor());
                out.print(p);
                out.print(AssignmentOrigin.BLANK);
                out.print(" ");
                stats[origin.ordinal()]++;
            }
            out.println("0");
            out.print(solver.getLogPrefix());
            for (AssignmentOrigin ao : AssignmentOrigin.values()) {
                out.printf("%s%s%s: %d ", ao.getColor(), ao,
                        AssignmentOrigin.BLANK, stats[ao.ordinal()]);
            }
            out.println();
        }
    }

    public void solve(IProblem problem, Reader reader, ILogAble logger,
            PrintWriter out, long beginTime) {
        this.exitCode = ExitCode.UNKNOWN;
        this.out = out;
        this.nbSolutionFound = 0;
        this.beginTime = beginTime;
        this.reader = reader;
        this.solver = (ISolver) problem;

        try {
            if (problem.isSatisfiable()) {
                if (this.exitCode == ExitCode.UNKNOWN) {
                    this.exitCode = ExitCode.SATISFIABLE;
                }
            } else {
                if (this.exitCode == ExitCode.UNKNOWN) {
                    this.exitCode = ExitCode.UNSATISFIABLE;
                }
            }
        } catch (TimeoutException e) {
            logger.log("timeout");
        }

    }

    public void setIncomplete(boolean isIncomplete) {
    }

    public ExitCode getCurrentExitCode() {
        return this.exitCode;
    }

    public void onSolutionFound(int[] solution) {
        this.nbSolutionFound++;
        this.exitCode = ExitCode.SATISFIABLE;
        this.out.printf("c Found solution #%d  (%.2f)s%n", nbSolutionFound,
                (System.currentTimeMillis() - beginTime) / 1000.0);
        if (System.getProperty("printallmodels") != null) {
            printSolution(solver, out, reader, solution);
        }
    }

    public void onSolutionFound(IVecInt solution) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void onUnsatTermination() {
        if (this.exitCode == ExitCode.SATISFIABLE) {
            this.exitCode = ExitCode.OPTIMUM_FOUND;
        }
    }

    public void setExitCode(ExitCode exitCode) {
        this.exitCode = exitCode;
    }
}