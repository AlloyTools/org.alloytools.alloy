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

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.GroupedCNFReader;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.AllMUSes;
import org.sat4j.tools.GroupClauseSelectorSolver;
import org.sat4j.tools.SolutionFoundListener;
import org.sat4j.tools.xplain.Explainer;
import org.sat4j.tools.xplain.HighLevelXplain;
import org.sat4j.tools.xplain.MinimizationStrategy;
import org.sat4j.tools.xplain.Xplain;

public class MUSLauncher extends AbstractLauncher {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private int[] mus;

    private Explainer xplain;

    private boolean highLevel = false;

    private AllMUSes allMuses;

    @Override
    public void usage() {
        log("java -jar sat4j-mus.jar [Insertion|Deletion|QuickXplain|all] <cnffile>|<gcnffile>");
    }

    @Override
    protected Reader createReader(ISolver theSolver, String problemname) {
        if (this.highLevel) {
            return new GroupedCNFReader(
                    (GroupClauseSelectorSolver<ISolver>) theSolver);
        }
        return new LecteurDimacs(theSolver);
    }

    @Override
    protected String getInstanceName(String[] args) {
        if (args.length == 0) {
            return null;
        }
        return args[args.length - 1];
    }

    @Override
    protected ISolver configureSolver(String[] args) {
        String problemName = args[args.length - 1];
        if (problemName.endsWith(".gcnf")) {
            this.highLevel = true;
        }
        ISolver solver;
        if (this.highLevel) {
            HighLevelXplain<ISolver> hlxp = new HighLevelXplain<ISolver>(
                    SolverFactory.newDefault());
            this.xplain = hlxp;
            solver = hlxp;
        } else {
            Xplain<ISolver> xp = new Xplain<ISolver>(SolverFactory.newDefault(),
                    false);
            this.xplain = xp;
            solver = xp;
        }
        solver.setDBSimplificationAllowed(true);
        if (args.length == 2) {
            // retrieve minimization strategy
            if ("all".equals(args[0])) {
                allMuses = new AllMUSes(highLevel, SolverFactory.instance());
                solver = allMuses.getSolverInstance();
            } else {
                String className = "org.sat4j.tools.xplain." + args[0]
                        + "Strategy";
                try {
                    this.xplain.setMinimizationStrategy(
                            (MinimizationStrategy) Class.forName(className)
                                    .newInstance());
                } catch (Exception e) {
                    log(e.getMessage());
                }
            }
        }
        solver.setTimeout(Integer.MAX_VALUE);
        getLogWriter().println(solver.toString(COMMENT_PREFIX));
        return solver;
    }

    @Override
    protected void displayResult() {
        if (this.solver != null) {
            double wallclocktime = (System.currentTimeMillis() - this.beginTime)
                    / 1000.0;
            this.solver.printStat(this.out);
            this.solver.printInfos(this.out);
            this.out.println(ILauncherMode.ANSWER_PREFIX + this.getExitCode());
            if (this.getExitCode() == ExitCode.SATISFIABLE) {
                int[] model = this.solver.model();
                this.out.print(ILauncherMode.SOLUTION_PREFIX);
                this.reader.decode(model, this.out);
                this.out.println();
            } else if (this.getExitCode() == ExitCode.UNSATISFIABLE
                    && this.mus != null) {
                this.out.print(ILauncherMode.SOLUTION_PREFIX);
                this.reader.decode(this.mus, this.out);
                this.out.println();
            }
            log("Total wall clock time (in seconds) : " + wallclocktime); //$NON-NLS-1$
        }
    }

    @Override
    public void run(String[] args) {
        this.mus = null;
        super.run(args);
        double wallclocktime = (System.currentTimeMillis() - this.beginTime)
                / 1000.0;
        if (this.getExitCode() == ExitCode.UNSATISFIABLE) {
            try {
                log("Unsat detection wall clock time (in seconds) : "
                        + wallclocktime);
                double beginmus = System.currentTimeMillis();
                if (allMuses != null) {
                    SolutionFoundListener mssListener = new SolutionFoundListener() {
                        private int msscount = 0;

                        public void onUnsatTermination() {
                            throw new UnsupportedOperationException(
                                    "Not implemented yet!");
                        }

                        public void onSolutionFound(IVecInt solution) {
                            System.out.print("\r" + solver.getLogPrefix()
                                    + "found mss number " + ++msscount);
                        }

                        public void onSolutionFound(int[] solution) {
                            throw new UnsupportedOperationException(
                                    "Not implemented yet!");
                        }
                    };
                    SolutionFoundListener musListener = new SolutionFoundListener() {
                        public void onSolutionFound(int[] solution) {
                        }

                        public void onSolutionFound(IVecInt solution) {
                            System.out.println(solver.getLogPrefix()
                                    + "found mus number " + ++muscount);
                            out.print(ILauncherMode.SOLUTION_PREFIX);
                            int[] localMus = new int[solution.size()];
                            solution.copyTo(localMus);
                            reader.decode(localMus, out);
                            out.println();
                        }

                        public void onUnsatTermination() {
                        }
                    };
                    allMuses.computeAllMSS(mssListener);
                    if ("card".equals(System.getProperty("min"))) {
                        allMuses.computeAllMUSesOrdered(musListener);
                    } else {
                        allMuses.computeAllMUSes(musListener);
                    }
                    log("All MUSes computation wall clock time (in seconds) : "
                            + (System.currentTimeMillis() - beginmus) / 1000.0);
                } else {
                    log("Size of initial "
                            + (this.highLevel ? "high level " : "")
                            + "unsat subformula: "
                            + this.solver.unsatExplanation().size());
                    log("Computing " + (this.highLevel ? "high level " : "")
                            + "MUS ...");
                    this.mus = this.xplain.minimalExplanation();
                    log("Size of the " + (this.highLevel ? "high level " : "")
                            + "MUS: " + this.mus.length);
                    log("Unsat core  computation wall clock time (in seconds) : "
                            + (System.currentTimeMillis() - beginmus) / 1000.0);
                }
            } catch (TimeoutException e) {
                log("Cannot compute " + (this.highLevel ? "high level " : "")
                        + "MUS within the timeout.");
            }
        }

    }

    private int muscount = 0;

    public static void main(final String[] args) {
        MUSLauncher lanceur = new MUSLauncher();
        if (args.length < 1 || args.length > 2) {
            lanceur.usage();
            return;
        }
        lanceur.addHook();
        lanceur.run(args);
        System.exit(lanceur.getExitCode().value());
    }
}
