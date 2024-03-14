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

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.file.Files;

import kodkod.engine.satlab.SATFactory;


/**
 * Mutable; this class encapsulates the customizable options of the
 * Alloy-to-Kodkod translator.
 *
 * @modified [electrum] electrod smv solvers; decompose strategy options, mode
 *           and cores
 */

public final class A4Options implements Serializable {

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Constructs an A4Options object with default values for everything.
     */
    public A4Options() {
    }

    public boolean    inferPartialInstance = true;

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
    public int        symmetry             = 20;

    /**
     * This option specifies the maximum skolem-function depth.
     * <p>
     * Default value is 0, which means it will only generate skolem constants, and
     * will not generate skolem functions.
     */
    public int        skolemDepth          = 0;

    /**
     * This option specifies the unsat core minimization strategy
     * (0=GuaranteedLocalMinimum 1=FasterButLessAccurate 2=EvenFaster...)
     * <p>
     * Default value is set to the fastest current strategy.
     */
    public int        coreMinimization     = 2;

    /**
     * Unsat core granularity, default is 0 (only top-level conjuncts are
     * considered), 3 expands all quantifiers
     */
    public int        coreGranularity      = 0;

    /**
     * This option specifies the SAT solver to use (SAT4J, MiniSatJNI,
     * MiniSatProverJNI, ZChaffJNI...)
     * <p>
     * Default value is SAT4J.
     */
    public SATFactory solver               = SATFactory.DEFAULT;

    /**
     * When this.solver is external, and the solver filename is a relative filename,
     * then this option specifies the directory that the solver filename is relative
     * to.
     */
    public String     solverDirectory      = "";

    /**
     * This specifies the directory where we may write temporary files to.
     */
    public String     tempDirectory        = System.getProperty("java.io.tmpdir");

    /**
     * This option tells the compiler the "original filename" that these AST nodes
     * came from; it is only used for generating comments and other diagnostic
     * messages.
     * <p>
     * Default value is "".
     */
    public String     originalFilename     = "";

    /**
     * This option specifies whether the compiler should record the original Kodkod
     * formula being generated and the resulting Kodkod instances.
     * <p>
     * Default value is false.
     */
    public boolean    recordKodkod         = false;

    /**
     * This option specifies whether the solver should report only solutions that
     * don't cause any overflows.
     */
    public boolean    noOverflow           = false;

    /**
     * This option constrols how deep we unroll loops and unroll recursive
     * predicate/function/macros (negative means it's disallowed)
     */
    public int        unrolls              = (-1);

    /**
     * This option specifies the decompose strategy (0=Off 1=Hybrid 2=Parallel)
     * <p>
     * Default value is off.
     */
    public int        decompose_mode       = 0;

    /**
     * This option specifies the number of threads when following a decompose
     * strategy
     * <p>
     * Default value is 4.
     */
    public int        decompose_threads    = 4;

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
        x.decompose_mode = decompose_mode;
        x.decompose_threads = decompose_threads;
        return x;
    }

    public File tempFile(String extension) throws IOException {
        File f = new File(tempDirectory);
        return Files.createTempFile(f.toPath(), "alloy", extension).toFile();
    }

}
