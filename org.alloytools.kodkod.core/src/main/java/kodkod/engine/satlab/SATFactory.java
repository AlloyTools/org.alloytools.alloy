/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.satlab;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.sat4j.minisat.SolverFactory;

/**
 * A factory for generating SATSolver instances of a given type. Built-in
 * support is provided for <a href="http://www.sat4j.org/">SAT4J solvers</a>,
 * the <a href= "http://www.princeton.edu/~chaff/zchaff.html">zchaff</a> solver
 * from Princeton, and the <a href=
 * "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/">MiniSat</a>
 * solver by Niklas E&eacute;n and Niklas S&ouml;rensson.
 *
 * @author Emina Torlak
 */
public abstract class SATFactory {

    /**
     * Constructs a new instance of SATFactory.
     */
    protected SATFactory() {}

    /**
     * Returns true iff the given factory generates solvers that are available for
     * use on this system.
     *
     * @return true iff the given factory generates solvers that are available for
     *         use on this system.
     */
    public static final boolean available(SATFactory factory) {
        SATSolver solver = null;
        try {
            solver = factory.instance();
            solver.addVariables(1);
            solver.addClause(new int[] {
                                        1
            });
            return solver.solve();
        } catch (RuntimeException e) {
            return false;
        } catch (UnsatisfiedLinkError t) {
            return false;
        } finally {
            if (solver != null) {
                solver.free();
            }
        }
    }

    /**
     * The factory that produces instances of the default sat4j solver.
     *
     * @see org.sat4j.core.ASolverFactory#defaultSolver()
     */
    public static final SATFactory DefaultSAT4J  = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new SAT4J(SolverFactory.instance().defaultSolver());
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "DefaultSAT4J";
                                                     }
                                                 };

    /**
     * The factory that produces instances of the "light" sat4j solver. The light
     * solver is suitable for solving many small instances of SAT problems.
     *
     * @see org.sat4j.core.ASolverFactory#lightSolver()
     */
    public static final SATFactory LightSAT4J    = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new SAT4J(SolverFactory.instance().lightSolver());
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "LightSAT4J";
                                                     }
                                                 };

    /**
     * The factory that produces instances of Niklas E&eacute;n and Niklas
     * S&ouml;rensson's MiniSat solver.
     */
    public static final SATFactory MiniSat       = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new MiniSat();
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "MiniSat";
                                                     }
                                                 };

    /**
     * The factory the produces {@link SATProver proof logging} instances of the
     * MiniSat solver. Note that core extraction can incur a significant time
     * overhead during solving, so if you do not need this functionality, use the
     * {@link #MiniSat} factory instead.
     */
    public static final SATFactory MiniSatProver = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new MiniSatProver();
                                                     }

                                                     @Override
                                                     public boolean prover() {
                                                         return true;
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "MiniSatProver";
                                                     }
                                                 };

    /**
     * The factory that produces instances of G. Audemard and L. Simon's Glucose
     * solver.
     */
    public static final SATFactory Glucose       = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new Glucose();
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "Glucose";
                                                     }
                                                 };

    /**
     * The factory that produces instances of G. Audemard and L. Simon's Glucose
     * solver.
     */
    public static final SATFactory Glucose41     = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new Glucose41();
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "Glucose41";
                                                     }
                                                 };

    /**
     * The factory that produces instances of the CryptoMiniSat solver by Mate Soos.
     */
    public static final SATFactory CryptoMiniSat = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new CryptoMiniSat();
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "CryptoMiniSat";
                                                     }
                                                 };

    /**
     * The factory that produces instances of Armin Biere's Lingeling solver.
     */
    public static final SATFactory Lingeling     = new SATFactory() {

                                                     @Override
                                                     public SATSolver instance() {
                                                         return new Lingeling();
                                                     }

                                                     @Override
                                                     public boolean incremental() {
                                                         return false;
                                                     }

                                                     @Override
                                                     public String toString() {
                                                         return "Lingeling";
                                                     }
                                                 };

    /**
     * Returns a SATFactory that produces SATSolver wrappers for Armin Biere's
     * Plingeling solver. This is a parallel solver that is invoked as an external
     * program rather than via the Java Native Interface. As a result, it cannot be
     * used incrementally. Its external factory manages the creation and deletion of
     * temporary files automatically. A statically compiled version of plingeling is
     * assumed to be available in a java.library.path directory. The effect of this
     * method is the same as calling {@link #plingeling(Integer, Boolean)
     * plingeling(null, null)}.
     *
     * @return SATFactory that produces SATSolver wrappers for the Plingeling solver
     */
    public static final SATFactory plingeling() {
        return plingeling(null, null);
    }

    /**
     * Returns a SATFactory that produces SATSolver wrappers for Armin Biere's
     * Plingeling solver. This is a parallel solver that is invoked as an external
     * program rather than via the Java Native Interface. As a result, it cannot be
     * used incrementally. Its external factory manages the creation and deletion of
     * temporary files automatically. A statically compiled version of plingeling is
     * assumed to be available in a java.library.path directory.
     * <p>
     * Plingling takes as input two optional parameters: {@code threads}, specifying
     * how many worker threads to use, and {@code portfolio}, specifying whether the
     * threads should run in portfolio mode (no sharing of clauses) or sharing mode.
     * If {@code threads} is null, the solver uses one worker per core. If
     * {@code portfolio} is null, it is set to true by default.
     * </p>
     *
     * @requires threads != null => numberOfThreads > 0
     * @return SATFactory that produces SATSolver wrappers for the Plingeling solver
     */
    public static final SATFactory plingeling(Integer threads, Boolean portfolio) {

        final List<String> opts = new ArrayList<String>(3);
        if (threads != null) {
            if (threads < 1)
                throw new IllegalArgumentException("Number of threads must be at least 1: numberOfThreads=" + threads);
            opts.add("-t");
            opts.add(threads.toString());
        }
        if (portfolio != null && portfolio)
            opts.add("-p");

        final String executable = findStaticLibrary("plingeling");
        return externalFactory(executable == null ? "plingeling" : executable, null, opts.toArray(new String[opts.size()]));

    }

    /**
     * Searches the {@code java.library.path} for an executable with the given name.
     * Returns a fully qualified path to the first found executable. Otherwise
     * returns null.
     *
     * @return a fully qualified path to an executable with the given name, or null
     *         if no executable is found.
     */
    private static String findStaticLibrary(String name) {
        final String[] dirs = System.getProperty("java.library.path").split(System.getProperty("path.separator"));

        for (int i = dirs.length - 1; i >= 0; i--) {
            final File file = new File(dirs[i] + File.separator + name);
            if (file.canExecute())
                return file.getAbsolutePath();
        }

        return null;
    }

    /**
     * Returns a SATFactory that produces instances of the specified SAT4J solver.
     * For the list of available SAT4J solvers see
     * {@link org.sat4j.core.ASolverFactory#solverNames()
     * org.sat4j.core.ASolverFactory#solverNames()}.
     *
     * @requires solverName is a valid solver name
     * @return a SATFactory that returns the instances of the specified SAT4J solver
     * @see org.sat4j.core.ASolverFactory#solverNames()
     */
    public static final SATFactory sat4jFactory(final String solverName) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                return new SAT4J(SolverFactory.instance().createSolverByName(solverName));
            }

            @Override
            public String toString() {
                return solverName;
            }
        };
    }

    /**
     * Returns a SATFactory that produces SATSolver wrappers for the external SAT
     * solver specified by the executable parameter. The solver's input and output
     * formats must conform to the
     * <a href= "http://www.satcompetition.org/2011/rules.pdf">SAT competition
     * standards</a>. The solver will be called with the specified options, and it
     * is expected to write properly formatted output to standard out. If the
     * {@code cnf} string is non-null, it will be used as the file name for
     * generated CNF files by all solver instances that the factory generates. If
     * {@code cnf} null, each solver instance will use an automatically generated
     * temporary file, which will be deleted when the solver instance is
     * garbage-collected. The {@code cnf} file, if provided, is not automatically
     * deleted; it is the caller's responsibility to delete it when no longer
     * needed. External solvers are never incremental.
     *
     * @return SATFactory that produces SATSolver wrappers for the specified
     *         external SAT solver
     */
    public static final SATFactory externalFactory(final String executable, final String cnf, final String... options) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                if (cnf != null) {
                    return new ExternalSolver(executable, cnf, false, options);
                } else {
                    try {
                        return new ExternalSolver(executable, File.createTempFile("kodkod", String.valueOf(executable.hashCode())).getAbsolutePath(), true, options);
                    } catch (IOException e) {
                        throw new SATAbortedException("Could not create a temporary file.", e);
                    }
                }
            }

            @Override
            public boolean incremental() {
                return false;
            }

            @Override
            public String toString() {
                return (new File(executable)).getName();
            }
        };
    }

    /**
     * Returns an instance of a SATSolver produced by this factory.
     *
     * @return a SATSolver instance
     */
    public abstract SATSolver instance();

    /**
     * Returns true if the solvers returned by this.instance() are {@link SATProver
     * SATProvers}. Otherwise returns false.
     *
     * @return true if the solvers returned by this.instance() are {@link SATProver
     *         SATProvers}. Otherwise returns false.
     */
    public boolean prover() {
        return false;
    }

    /**
     * Returns true if the solvers returned by this.instance() are incremental; i.e.
     * if clauses/variables can be added to the solver between multiple calls to
     * solve().
     *
     * @return true if the solvers returned by this.instance() are incremental
     */
    public boolean incremental() {
        return true;
    }

}
