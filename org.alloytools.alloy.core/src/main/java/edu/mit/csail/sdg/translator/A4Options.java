/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import java.io.Serializable;

import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.SafeList;

/**
 * Mutable; this class encapsulates the customizable options of the
 * Alloy-to-Kodkod translator.
 */

public final class A4Options implements Serializable {

    /** This enum defines the set of possible SAT solvers. */
    public static final class SatSolver implements Serializable {

        /** This ensures the class can be serialized reliably. */
        private static final long                serialVersionUID = 0;
        /** List of all existing SatSolver values. */
        private static final SafeList<SatSolver> values           = new SafeList<SatSolver>();
        /**
         * This is a unique String for this value; it should be kept consistent in
         * future versions.
         */
        private final String                     id;
        /**
         * This is the label that the toString() method will return.
         */
        private final String                     toString;
        /**
         * If not null, this is the external command-line solver to use.
         */
        private final String                     external;
        /**
         * If not null, this is the set of options to use with the command-line solver.
         */
        private final String[]                   options;

        /** Constructs a new SatSolver value. */
        private SatSolver(String id, String toString, String external, String[] options, boolean add) {
            this.id = id;
            this.toString = toString;
            this.external = external;
            this.options = new String[options != null ? options.length : 0];
            for (int i = 0; i < this.options.length; i++)
                this.options[i] = options[i];
            if (add) {
                synchronized (SatSolver.class) {
                    values.add(this);
                }
            }
        }

        /**
         * Constructs a new SatSolver value that uses a command-line solver; throws
         * ErrorAPI if the ID is already in use.
         */
        public static SatSolver make(String id, String toString, String external, String[] options) throws ErrorAPI {
            if (id == null || toString == null || external == null)
                throw new ErrorAPI("NullPointerException in SatSolver.make()");
            SatSolver ans = new SatSolver(id, toString, external, options, false);
            synchronized (SatSolver.class) {
                for (SatSolver x : values)
                    if (x.id.equals(id))
                        throw new ErrorAPI("The SatSolver id \"" + id + "\" is already in use.");
                values.add(ans);
            }
            return ans;
        }

        /**
         * Constructs a new SatSolver value that uses a command-line solver; throws
         * ErrorAPI if the ID is already in use.
         */
        public static SatSolver make(String id, String toString, String external) throws ErrorAPI {
            return make(id, toString, external, null);
        }

        /**
         * Returns the executable for the external command-line solver to use (or null
         * if this solver does not use an external commandline solver)
         */
        public String external() {
            return external;
        }

        /**
         * Returns the options for the external command-line solver to use (or empty
         * array if this solver does not use an external commandline solver)
         */
        public String[] options() {
            if (external == null || options.length == 0)
                return new String[0];
            String[] ans = new String[options.length];
            for (int i = 0; i < ans.length; i++)
                ans[i] = options[i];
            return ans;
        }

        /**
         * Returns the unique String for this value; it will be kept consistent in
         * future versions.
         */
        public String id() {
            return id;
        }

        /** Returns the list of SatSolver values. */
        public static SafeList<SatSolver> values() {
            SafeList<SatSolver> ans;
            synchronized (SatSolver.class) {
                ans = values.dup();
            }
            return ans;
        }

        /** Returns the human-readable label for this enum value. */
        @Override
        public String toString() {
            return toString;
        }

        /** Ensures we can use == to do comparison. */
        private Object readResolve() {
            synchronized (SatSolver.class) {
                for (SatSolver x : values)
                    if (x.id.equals(id))
                        return x;
                values.add(this);
            }
            return this;
        }

        /**
         * Given an id, return the enum value corresponding to it (if there's no match,
         * then return SAT4J).
         */
        public static SatSolver parse(String id) {
            synchronized (SatSolver.class) {
                for (SatSolver x : values)
                    if (x.id.equals(id))
                        return x;
            }
            return SAT4J;
        }

        /** BerkMin via pipe */
        public static final SatSolver BerkMinPIPE      = new SatSolver("berkmin", "BerkMin", "berkmin", null, true);
        /** Spear via pipe */
        public static final SatSolver SpearPIPE        = new SatSolver("spear", "Spear", "spear", new String[] {
                                                                                                                "--model", "--dimacs"
        }, true);
        /** MiniSat1 via JNI */
        public static final SatSolver MiniSatJNI       = new SatSolver("minisat(jni)", "MiniSat", null, null, true);
        /** MiniSatProver1 via JNI */
        public static final SatSolver MiniSatProverJNI = new SatSolver("minisatprover(jni)", "MiniSat with Unsat Core", null, null, true);
        /// ** ZChaff via JNI */
        // public static final SatSolver ZChaffJNI = new
        /// SatSolver("zchaff(jni)", "ZChaff with mincost", null, null, true);
        /** Lingeling */
        public static final SatSolver LingelingJNI     = new SatSolver("lingeling(jni)", "Lingeling", null, null, true);
        public static final SatSolver PLingelingJNI    = new SatSolver("plingeling(jni)", "PLingeling", null, null, true);
        /** Glucose */
        public static final SatSolver GlucoseJNI       = new SatSolver("glucose(jni)", "Glucose", null, null, true);
        public static final SatSolver Glucose41JNI     = new SatSolver("glucose 4.1(jni)", "Glucose41", null, null, true);
        /** CryptoMiniSat */
        public static final SatSolver CryptoMiniSatJNI = new SatSolver("cryptominisat(jni)", "CryptoMiniSat", null, null, true);
        /** SAT4J using native Java */
        public static final SatSolver SAT4J            = new SatSolver("sat4j", "SAT4J", null, null, true);
        /** Outputs the raw CNF file only */
        public static final SatSolver CNF              = new SatSolver("cnf", "Output CNF to file", null, null, true);
        /** Outputs the raw Kodkod file only */
        public static final SatSolver KK               = new SatSolver("kodkod", "Output Kodkod to file", null, null, true);

    }

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Constructs an A4Options object with default values for everything.
     */
    public A4Options() {}

    public boolean   inferPartialInstance = true;

    /**
     * This option specifies the amount of symmetry breaking to do (when symmetry
     * breaking isn't explicitly disabled).
     * <p>
     * If a formula is unsatisfiable, then in general, the higher this value, the
     * faster you finish the solving. But if this value is too high, it will instead
     * slow down the solving.
     * <p>
     * If a formula is satisfiable, then in general, the lower this value, the
     * faster you finish the solving. Setting this value to 0 usually gives the
     * fastest solve.
     * <p>
     * Default value is 20.
     */
    public int       symmetry             = 20;

    /**
     * This option specifies the maximum skolem-function depth.
     * <p>
     * Default value is 0, which means it will only generate skolem constants, and
     * will not generate skolem functions.
     */
    public int       skolemDepth          = 0;

    /**
     * This option specifies the unsat core minimization strategy
     * (0=GuaranteedLocalMinimum 1=FasterButLessAccurate 2=EvenFaster...)
     * <p>
     * Default value is set to the fastest current strategy.
     */
    public int       coreMinimization     = 2;

    /**
     * Unsat core granularity, default is 0 (only top-level conjuncts are
     * considered), 3 expands all quantifiers
     */
    public int       coreGranularity      = 0;

    /**
     * This option specifies the SAT solver to use (SAT4J, MiniSatJNI,
     * MiniSatProverJNI, ZChaffJNI...)
     * <p>
     * Default value is SAT4J.
     */
    public SatSolver solver               = SatSolver.SAT4J;

    /**
     * When this.solver is external, and the solver filename is a relative filename,
     * then this option specifies the directory that the solver filename is relative
     * to.
     */
    public String    solverDirectory      = "";

    /**
     * This specifies the directory where we may write temporary files to.
     */
    public String    tempDirectory        = System.getProperty("java.io.tmpdir");

    /**
     * This option tells the compiler the "original filename" that these AST nodes
     * came from; it is only used for generating comments and other diagnostic
     * messages.
     * <p>
     * Default value is "".
     */
    public String    originalFilename     = "";

    /**
     * This option specifies whether the compiler should record the original Kodkod
     * formula being generated and the resulting Kodkod instances.
     * <p>
     * Default value is false.
     */
    public boolean   recordKodkod         = false;

    /**
     * This option specifies whether the solver should report only solutions that
     * don't cause any overflows.
     */
    public boolean   noOverflow           = false;

    /**
     * This option constrols how deep we unroll loops and unroll recursive
     * predicate/function/macros (negative means it's disallowed)
     */
    public int       unrolls              = (-1);

    /** This method makes a copy of this Options object. */
    public A4Options dup() {
        A4Options x = new A4Options();
        x.inferPartialInstance = inferPartialInstance;
        x.unrolls = unrolls;
        x.symmetry = symmetry;
        x.skolemDepth = skolemDepth;
        x.coreMinimization = coreMinimization;
        x.solver = solver;
        x.solverDirectory = solverDirectory;
        x.tempDirectory = tempDirectory;
        x.originalFilename = originalFilename;
        x.recordKodkod = recordKodkod;
        x.noOverflow = noOverflow;
        x.coreGranularity = coreGranularity;
        return x;
    }
}
