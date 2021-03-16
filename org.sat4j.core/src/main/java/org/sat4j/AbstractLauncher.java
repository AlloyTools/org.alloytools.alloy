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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.ObjectInputStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.net.URL;
import java.util.Properties;

import org.sat4j.core.ASolverFactory;
import org.sat4j.minisat.core.ICDCL;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.orders.OrientedOrder;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ILogAble;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.DotSearchTracing;
import org.sat4j.tools.ModelIteratorToSATAdapter;
import org.sat4j.tools.RupSearchListener;
import org.sat4j.tools.SearchEnumeratorListener;
import org.sat4j.tools.SearchMinOneListener;
import org.sat4j.tools.SolverDecorator;

/**
 * That class is used by launchers used to solve decision problems, i.e.
 * problems with YES/NO/UNKNOWN answers.
 * 
 * @author leberre
 * 
 */
public abstract class AbstractLauncher implements Serializable, ILogAble {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public static final String COMMENT_PREFIX = "c "; //$NON-NLS-1$

    protected long beginTime;

    protected transient Reader reader;

    protected boolean feedWithDecorated = false;

    protected transient PrintWriter out = new PrintWriter(System.out, true);

    private StringBuilder logBuffer;

    private boolean displaySolutionLine = true;

    protected transient Thread shutdownHook = new Thread() {
        @Override
        public void run() {
            // stop the solver before displaying solutions
            if (solver != null) {
                solver.expireTimeout();
            }
            displayResult();
        }
    };

    protected ISolver solver;

    protected IProblem problem;

    private boolean silent = false;

    protected boolean prime = System.getProperty("prime") != null;

    private ILauncherMode launcherMode = ILauncherMode.DECISION;

    protected void setLauncherMode(ILauncherMode launcherMode) {
        this.launcherMode = launcherMode;
    }

    protected ILauncherMode getLauncherMode() {
        return this.launcherMode;
    }

    protected void setIncomplete(boolean isIncomplete) {
        this.launcherMode.setIncomplete(isIncomplete);
    }

    public final void addHook() {
        Runtime.getRuntime().addShutdownHook(this.shutdownHook);
    }

    protected void displayResult() {
        launcherMode.displayResult(solver, problem, this, out, reader,
                beginTime, displaySolutionLine);
    }

    public abstract void usage();

    protected final void displayHeader() {
        displayLicense();
        URL url = AbstractLauncher.class.getResource("/sat4j.version"); //$NON-NLS-1$
        if (url == null) {
            log("no version file found!!!"); //$NON-NLS-1$
        } else {
            try (BufferedReader in = new BufferedReader(
                    new InputStreamReader(url.openStream()))) {
                log("version " + in.readLine()); //$NON-NLS-1$
            } catch (IOException e) {
                log("c ERROR: " + e.getMessage());
            }
        }
        Properties prop = System.getProperties();
        String[] infoskeys = { "java.runtime.name", "java.vm.name", //$NON-NLS-1$//$NON-NLS-2$
                "java.vm.version", "java.vm.vendor", "sun.arch.data.model", //$NON-NLS-1$ //$NON-NLS-2$//$NON-NLS-3$
                "java.version", "os.name", "os.version", "os.arch" };
        for (String key : infoskeys) {
            log(key + (key.length() < 14 ? "\t\t" : "\t") //$NON-NLS-1$
                    + prop.getProperty(key));
        }
        Runtime runtime = Runtime.getRuntime();
        log("Free memory \t\t" + runtime.freeMemory()); //$NON-NLS-1$
        log("Max memory \t\t" + runtime.maxMemory()); //$NON-NLS-1$
        log("Total memory \t\t" + runtime.totalMemory()); //$NON-NLS-1$
        log("Number of processors \t" + runtime.availableProcessors()); //$NON-NLS-1$
    }

    public void displayLicense() {
        log("SAT4J: a SATisfiability library for Java (c) 2004-2013 Artois University and CNRS"); //$NON-NLS-1$
        log("This is free software under the dual EPL/GNU LGPL licenses."); //$NON-NLS-1$
        log("See www.sat4j.org for details."); //$NON-NLS-1$
    }

    /**
     * Reads a problem file from the command line.
     * 
     * @param problemname
     *            the fully qualified name of the problem.
     * @return a reference to the problem to solve
     * @throws ParseFormatException
     *             if the problem is not expressed using the right format
     * @throws IOException
     *             for other IO problems
     * @throws ContradictionException
     *             if the problem is found trivially unsat
     */
    protected IProblem readProblem(String problemname)
            throws ParseFormatException, IOException, ContradictionException {
        log("solving " + problemname); //$NON-NLS-1$
        log("reading problem ... "); //$NON-NLS-1$
        SolverDecorator<ISolver> decorator = null;
        ISolver originalProblem;
        if (feedWithDecorated) {
            decorator = (SolverDecorator<ISolver>) this.solver;
            originalProblem = decorator.decorated();
        } else {
            originalProblem = this.solver;
        }
        this.reader = createReader(originalProblem, problemname);
        IProblem aProblem = this.reader.parseInstance(problemname);
        if (this.reader.hasAMapping()) {
            SearchListener<?> listener = this.solver.getSearchListener();
            if (listener instanceof DotSearchTracing) {
                ((DotSearchTracing) listener)
                        .setMapping(this.reader.getMapping());
            }
        }
        log("... done. Wall clock time " //$NON-NLS-1$
                + (System.currentTimeMillis() - this.beginTime) / 1000.0
                + "s."); //$NON-NLS-1$
        log("declared #vars     " + aProblem.nVars()); //$NON-NLS-1$
        if (this.solver.nVars() < this.solver.realNumberOfVariables()) {
            log("internal #vars     " + this.solver.realNumberOfVariables()); //$NON-NLS-1$
        }
        log("#constraints  " + aProblem.nConstraints()); //$NON-NLS-1$
        aProblem.printInfos(this.out);
        if (System.getProperty("UNSATPROOF") != null) {
            String proofFile = problemname + ".rupproof";
            this.solver.setSearchListener(
                    new RupSearchListener<ISolverService>(proofFile));
            if (!this.isSilent()) {
                System.out.println(this.solver.getLogPrefix()
                        + "Generating unsat proof in file " + proofFile);
            }
        }
        if (System.getProperty("forceorder") != null) {
            String orderFile = problemname + ".order";
            ICDCL solverService = (ICDCL) solver;
            IOrder order = new OrientedOrder(orderFile,
                    solverService.getOrder());
            solverService.setOrder(order);
            if (!this.isSilent()) {
                System.out.println(this.solver.getLogPrefix()
                        + "Forcing heuristics using file " + orderFile);
            }
        }
        if (feedWithDecorated) {
            return decorator;
        }
        return aProblem;
    }

    protected abstract Reader createReader(ISolver theSolver,
            String problemname);

    public void run(String[] args) {

        try {
            displayHeader();
            this.solver = configureSolver(args);
            if (this.solver == null) {
                usage();
                return;
            }
            if (!this.isSilent()) {
                this.solver.setVerbose(true);
            }
            configureLauncher();
            String instanceName = getInstanceName(args);
            if (instanceName == null) {
                usage();
                return;
            }
            this.beginTime = System.currentTimeMillis();
            this.problem = readProblem(instanceName);
            solve(this.problem);
        } catch (TimeoutException e) {
            log("timeout"); //$NON-NLS-1$
        } catch (ContradictionException e) {
            this.launcherMode.setExitCode(ExitCode.UNSATISFIABLE);
            log("(trivial inconsistency)"); //$NON-NLS-1$
        } catch (IOException | ParseFormatException e) {
            System.err.println("FATAL " + e.getLocalizedMessage());
        }
    }

    protected void configureLauncher() {
        String all = System.getProperty("all");
        if (all != null) {
            if ("external".equals(all)) {
                feedWithDecorated = true;
                this.solver = new ModelIteratorToSATAdapter(this.solver,
                        launcherMode);
                System.out.println(this.solver.getLogPrefix()
                        + "model enumeration using the external way");
            } else {
                SearchEnumeratorListener enumerator = new SearchEnumeratorListener(
                        launcherMode);
                this.solver.setSearchListener(enumerator);
                System.out.println(this.solver.getLogPrefix()
                        + "model enumeration using the internal way");
            }
        }
        if (System.getProperty("minone") != null) {
            SearchMinOneListener minone = new SearchMinOneListener(
                    launcherMode);
            this.solver.setSearchListener(minone);
        }
    }

    protected abstract String getInstanceName(String[] args);

    protected abstract ISolver configureSolver(String[] args);

    /**
     * Display messages as comments on STDOUT
     * 
     * @param message
     *            a textual information
     */
    public void log(String message) {
        if (this.isSilent())
            return;
        if (this.logBuffer != null) {
            this.logBuffer.append(COMMENT_PREFIX).append(message).append('\n');
        } else {
            this.out.println(COMMENT_PREFIX + message);
        }
    }

    protected void solve(IProblem problem) throws TimeoutException {
        launcherMode.solve(problem, reader, this, out, beginTime);
    }

    /**
     * To change the display so that solution line appears or not. Recommended
     * if solution is very large.
     * 
     * @param value
     *            true to display the message
     */
    protected void setDisplaySolutionLine(boolean value) {
        this.displaySolutionLine = value;
    }

    /**
     * Change the value of the exit code in the Launcher
     * 
     * @param exitCode
     *            the new ExitCode
     */
    public final void setExitCode(ExitCode exitCode) {
        this.launcherMode.setExitCode(exitCode);
    }

    /**
     * Get the value of the ExitCode
     * 
     * @return the current value of the Exitcode
     */
    public final ExitCode getExitCode() {
        return this.launcherMode.getCurrentExitCode();
    }

    /**
     * Obtaining the current time spent since the beginning of the solving
     * process.
     * 
     * @return the time signature at the beginning of the run() method.
     */
    public final long getBeginTime() {
        return this.beginTime;
    }

    /**
     * 
     * @return the reader used to parse the instance
     */
    public final Reader getReader() {
        return this.reader;
    }

    /**
     * To change the output stream on which statistics are displayed. By
     * default, the solver displays everything on System.out.
     * 
     * @param out
     *            a new output for the statistics.
     */
    public void setLogWriter(PrintWriter out) {
        this.out = out;
    }

    public PrintWriter getLogWriter() {
        return this.out;
    }

    protected void setSilent(boolean b) {
        this.silent = b;
    }

    private void readObject(ObjectInputStream stream)
            throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        this.out = new PrintWriter(System.out, true);
        this.shutdownHook = new Thread() {
            @Override
            public void run() {
                displayResult();
            }
        };
    }

    protected <T extends ISolver> void showAvailableSolvers(
            ASolverFactory<T> afactory) {
        showAvailableSolvers(afactory, "");
    }

    protected <T extends ISolver> void showAvailableSolvers(
            ASolverFactory<T> afactory, String framework) {
        if (afactory != null) {
            if (framework.length() > 0) {
                log("Available solvers for " + framework + ": "); //$NON-NLS-1$
            } else {
                log("Available solvers: "); //$NON-NLS-1$
            }
            String[] names = afactory.solverNames();
            for (String name : names) {
                log(name);
            }
        }
    }

    protected void bufferizeLog() {
        this.logBuffer = new StringBuilder();
    }

    protected void flushLog() {
        if (logBuffer != null) {
            this.out.print(logBuffer.toString());
        }
        logBuffer = null;
    }

    public boolean isSilent() {
        return silent;
    }
}
