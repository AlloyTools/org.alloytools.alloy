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
package kodkod.engine.config;

import kodkod.engine.satlab.SATFactory;
import kodkod.util.ints.IntRange;
import kodkod.util.ints.Ints;

/**
 * Stores information about various user-level translation and analysis options.
 * It can be used to choose the SAT solver, control symmetry breaking, etc.
 *
 * @specfield solver: SATFactory // SAT solver factory to use
 * @specfield reporter: Reporter // reporter to use
 * @specfield symmetryBreaking: int // the amount of symmetry breaking to
 *            perform
 * @specfield sharing: int // the depth to which circuits should be checked for
 *            equivalence during translation
 * @specfield intEncoding: IntEncoding // encoding to use for translating int
 *            expressions
 * @specfield bitwidth: int // the bitwidth to use for integer representation /
 *            arithmetic
 * @specfield skolemDepth: int // skolemization depth
 * @specfield ofPolicy: OverflowPolicy // whether to detect and prevent or
 *            promote overflows.
 * @specfield logTranslation: [0..2] // log translation events, default is 0 (no
 *            logging)
 * @specfield coreGranularity: [0..3] // unsat core granularity, default is 0
 *            (only top-level conjuncts are considered)
 * @specfield allowHOL: boolean // allow higher-order quantification
 * @specfield holSome4AllMaxIter: boolean // allow higher-order quantification
 * @author Emina Torlak
 */
public final class Options implements Cloneable {

    public static enum OverflowPolicy {
                                       NONE,
                                       PREVENT,
                                       PROMOTE;

        public OverflowPolicy dual;

        static {
            NONE.dual = NONE;
            PREVENT.dual = PROMOTE;
            PROMOTE.dual = PREVENT;
        }
    }

    private Reporter       reporter           = new AbstractReporter() {};
    private SATFactory     solver             = SATFactory.DefaultSAT4J;
    private int            symmetryBreaking   = 20;
    private IntEncoding    intEncoding        = IntEncoding.TWOSCOMPLEMENT;
    private int            bitwidth           = 4;
    private int            sharing            = 3;
    private OverflowPolicy ofPolicy           = OverflowPolicy.NONE;
    private boolean        allowHOL           = false;
    private boolean        holFullIncrements  = true;
    private int            holSome4AllMaxIter = -1;
    private int            holFixpointMaxIter = -1;
    private int            skolemDepth        = 0;
    private int            logTranslation     = 0;
    private int            coreGranularity    = 0;

    // [AM]
    public static boolean isDebug() {
        return false; // TODO: read from the environment or something
    }

    /**
     * Constructs an Options object initialized with default values.
     *
     * @ensures this.solver' = SATFactory.DefaultSAT4J this.reporter' is silent (no
     *          messages reported) this.symmetryBreaking' = 20 this.sharing' = 3
     *          this.intEncoding' = BINARY this.bitwidth' = 4 this.skolemDepth' = 0
     *          this.logTranslation' = 0 this.coreGranularity' = 0 this.allowHOL =
     *          false this.holSome4AllMaxIter = -1
     */
    public Options() {}

    /**
     * Returns the value of the solver options. The default is
     * SATSolver.DefaultSAT4J.
     *
     * @return this.solver
     */
    public SATFactory solver() {
        return solver;
    }

    /**
     * Sets the solver option to the given value.
     *
     * @ensures this.solver' = solver
     * @throws NullPointerException solver = null
     */
    public void setSolver(SATFactory solver) {
        if (solver == null)
            throw new NullPointerException();
        this.solver = solver;
    }

    /**
     * Returns this.reporter.
     *
     * @return this.reporter
     */
    public Reporter reporter() {
        return reporter;
    }

    /**
     * Sets this.reporter to the given reporter.
     *
     * @requires reporter != null
     * @ensures this.reporter' = reporter
     * @throws NullPointerException reporter = null
     */
    public void setReporter(Reporter reporter) {
        if (reporter == null)
            throw new NullPointerException();
        this.reporter = reporter;
    }

    /** Returns the noOverflow flag */
    public boolean noOverflow() {
        return ofPolicy != OverflowPolicy.NONE;
    }

    /** Sets the noOverflow flag */
    public void setNoOverflow(boolean noOverflow) {
        this.ofPolicy = noOverflow ? OverflowPolicy.PREVENT : OverflowPolicy.NONE;
    }

    public OverflowPolicy overflowPolicy() {
        return ofPolicy;
    }

    public void setOverflowPolicy(OverflowPolicy ofPolicy) {
        this.ofPolicy = ofPolicy;
    }

    // [HOL]=======
    public boolean isAllowHOL() {
        return allowHOL;
    }

    public void setAllowHOL(boolean allowHOL) {
        this.allowHOL = allowHOL;
    }

    public boolean isHolFullIncrements() {
        return holFullIncrements;
    }

    public void setHolFullIncrements(boolean val) {
        this.holFullIncrements = val;
    }

    public int getHolSome4AllMaxIter() {
        return holSome4AllMaxIter;
    }

    public void setHolSome4AllMaxIter(int val) {
        this.holSome4AllMaxIter = val;
    }

    public int getHolFixpointMaxIter() {
        return holFixpointMaxIter;
    }

    public void setHolFixpointMaxIter(int val) {
        this.holFixpointMaxIter = val;
    }
    // ============

    /**
     * @throws IllegalArgumentException arg !in [min..max]
     */
    private void checkRange(int arg, int min, int max) {
        if (arg < min || arg > max)
            throw new IllegalArgumentException(arg + " !in [" + min + ".." + max + "]");
    }

    /**
     * Returns the integer encoding that will be used for translating
     * {@link kodkod.ast.IntExpression int nodes}. The default is BINARY
     * representation, which allows negative numbers. UNARY representation is best
     * suited to problems with small scopes, in which cardinalities are only
     * compared (and possibly added to each other or non-negative numbers).
     *
     * @return this.intEncoding
     */
    public IntEncoding intEncoding() {
        return intEncoding;
    }

    /**
     * Sets the intEncoding option to the given value.
     *
     * @ensures this.intEncoding' = encoding
     * @throws NullPointerException encoding = null
     * @throws IllegalArgumentException this.bitwidth is not a valid bitwidth for
     *             the specified encoding
     */
    public void setIntEncoding(IntEncoding encoding) {
        if (encoding.maxAllowedBitwidth() < bitwidth)
            throw new IllegalArgumentException();
        this.intEncoding = encoding;
    }

    /**
     * Returns the size of the integer representation. For example, if
     * this.intEncoding is BINARY and this.bitwidth = 5 (the default), then all
     * operations will yield one of the five-bit numbers in the range [-16..15]. If
     * this.intEncoding is UNARY and this.bitwidth = 5, then all operations will
     * yield one of the numbers in the range [0..5].
     *
     * @return this.bitwidth
     */
    public int bitwidth() {
        return bitwidth;
    }

    /**
     * Sets this.bitwidth to the given value.
     *
     * @ensures this.bitwidth' = bitwidth
     * @throws IllegalArgumentException bitwidth < 1
     * @throws IllegalArgumentException this.intEncoding==BINARY && bitwidth > 32
     */
    public void setBitwidth(int bitwidth) {
        checkRange(bitwidth, 1, intEncoding.maxAllowedBitwidth());
        this.bitwidth = bitwidth;
    }

    /**
     * Returns the range of integers that can be encoded using this.intEncoding and
     * this.bitwidth.
     *
     * @return range of integers that can be encoded using this.intEncoding and
     *         this.bitwidth.
     */
    public IntRange integers() {
        return intEncoding.range(bitwidth);
    }

    /**
     * Returns the 'amount' of symmetry breaking to perform. If a non-symmetric
     * solver is chosen for this.solver, this value controls the maximum length of
     * the generated lex-leader symmetry breaking predicate. In general, the higher
     * this value, the more symmetries will be broken. But setting the value too
     * high may have the opposite effect and slow down the solving. The default
     * value for this property is 20.
     *
     * @return this.symmetryBreaking
     */
    public int symmetryBreaking() {
        return symmetryBreaking;
    }

    /**
     * Sets the symmetryBreaking option to the given value.
     *
     * @ensures this.symmetryBreaking' = symmetryBreaking
     * @throws IllegalArgumentException symmetryBreaking !in [0..Integer.MAX_VALUE]
     */
    public void setSymmetryBreaking(int symmetryBreaking) {
        checkRange(symmetryBreaking, 0, Integer.MAX_VALUE);
        this.symmetryBreaking = symmetryBreaking;
    }

    /**
     * Returns the depth to which circuits are checked for equivalence during
     * translation. The default depth is 3, and the minimum allowed depth is 1.
     * Increasing the sharing may result in a smaller CNF, but at the cost of slower
     * translation times.
     *
     * @return this.sharing
     */
    public int sharing() {
        return sharing;
    }

    /**
     * Sets the sharing option to the given value.
     *
     * @ensures this.sharing' = sharing
     * @throws IllegalArgumentException sharing !in [1..Integer.MAX_VALUE]
     */
    public void setSharing(int sharing) {
        checkRange(sharing, 1, Integer.MAX_VALUE);
        this.sharing = sharing;
    }

    /**
     * Returns the depth to which existential quantifiers are skolemized. A negative
     * depth means that no skolemization is performed. The default depth of 0 means
     * that only existentials that are not nested within a universal quantifiers are
     * skolemized. A depth of 1 means that existentials nested within a single
     * universal are also skolemized, etc.
     *
     * @return this.skolemDepth
     */
    public int skolemDepth() {
        return skolemDepth;
    }

    /**
     * Sets the skolemDepth to the given value.
     *
     * @ensures this.skolemDepth' = skolemDepth
     */
    public void setSkolemDepth(int skolemDepth) {
        this.skolemDepth = skolemDepth;
    }

    /**
     * Returns the translation logging level (0, 1, or 2), where 0 means logging is
     * not performed, 1 means only the translations of top level formulas are
     * logged, and 2 means all formula translations are logged. This is necessary
     * for determining which formulas occur in the unsat core of an unsatisfiable
     * formula. Logging is off by default, since it incurs a non-trivial time
     * overhead.
     *
     * @return this.logTranslation
     */
    public int logTranslation() {
        return logTranslation;
    }

    /**
     * Sets the translation logging level.
     *
     * @requires logTranslation in [0..2]
     * @ensures this.logTranslation' = logTranslation
     * @throws IllegalArgumentException logTranslation !in [0..2]
     */
    public void setLogTranslation(int logTranslation) {
        checkRange(logTranslation, 0, 2);
        this.logTranslation = logTranslation;
    }

    /**
     * Returns the core granularity level. The default is 0, which means that
     * top-level conjuncts of the input formula are used as "roots" for the purposes
     * of core minimization and extraction. Granularity of 1 means that the
     * top-level conjuncts of the input formula's negation normal form (NNF) are
     * used as roots; granularity of 2 means that the top-level conjuncts of the
     * formula's skolemized NNF (SNNF) are used as roots; and, finally, a
     * granularity of 3 means that the universal quantifiers of the formula's SNNF
     * are broken up and that the resulting top-level conjuncts are then used as
     * roots for core minimization and extraction.
     * <p>
     * Note that the finer granularity (that is, a larger value of
     * this.coreGranularity) will provide better information at the cost of slower
     * core extraction and, in particular, minimization.
     * </p>
     *
     * @return this.coreGranularity
     */
    public int coreGranularity() {
        return coreGranularity;
    }

    /**
     * Sets the core granularity level.
     *
     * @requires coreGranularity in [0..3]
     * @ensures this.coreGranularity' = coreGranularity
     * @throws IllegalArgumentException coreGranularity !in [0..3]
     */
    public void setCoreGranularity(int coreGranularity) {
        checkRange(coreGranularity, 0, 3);
        this.coreGranularity = coreGranularity;
    }

    /**
     * Returns a shallow copy of this Options object. In particular, the returned
     * options shares the same {@linkplain #reporter()} and {@linkplain #solver()}
     * factory objects as this Options.
     *
     * @return a shallow copy of this Options object.
     */
    @Override
    public Options clone() {
        final Options c = new Options();
        c.setSolver(solver);
        c.setReporter(reporter);
        c.setBitwidth(bitwidth);
        c.setIntEncoding(intEncoding);
        c.setSharing(sharing);
        c.setSymmetryBreaking(symmetryBreaking);
        c.setSkolemDepth(skolemDepth);
        c.setLogTranslation(logTranslation);
        c.setCoreGranularity(coreGranularity);
        c.setOverflowPolicy(ofPolicy);
        c.setAllowHOL(allowHOL);
        c.setHolFullIncrements(holFullIncrements);
        c.setHolSome4AllMaxIter(holSome4AllMaxIter);
        c.setHolFixpointMaxIter(holFixpointMaxIter);
        return c;
    }

    /**
     * Returns a string representation of this Options object.
     *
     * @return a string representation of this Options object.
     */
    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("Options:");
        b.append("\n solver: ");
        b.append(solver);
        b.append("\n reporter: ");
        b.append(reporter);
        b.append("\n intEncoding: ");
        b.append(intEncoding);
        b.append("\n bitwidth: ");
        b.append(bitwidth);
        b.append("\n sharing: ");
        b.append(sharing);
        b.append("\n symmetryBreaking: ");
        b.append(symmetryBreaking);
        b.append("\n skolemDepth: ");
        b.append(skolemDepth);
        b.append("\n logTranslation: ");
        b.append(logTranslation);
        b.append("\n coreGranularity: ");
        b.append(coreGranularity);
        b.append("\n noOverflow: ");
        b.append(ofPolicy);
        b.append("\n allowHOL: ");
        b.append(allowHOL);
        b.append("\n holFullIncrements: ");
        b.append(holFullIncrements);
        b.append("\n holSome4AllMaxIter: ");
        b.append(holSome4AllMaxIter);
        b.append("\n holFixpointMaxIter: ");
        b.append(holFixpointMaxIter);
        return b.toString();
    }

    /**
     * Integer encoding options for the translation of
     * {@link kodkod.ast.IntExpression int expressions}.
     */
    public static enum IntEncoding {
                                    /**
                                     * Two's-complement encoding of integers supports comparisons, addition,
                                     * subtraction, multiplication, division, and all low-level bit operations
                                     * (shifting, and, or, not, etc.). Maximum allowed bitwidth for this encoding is
                                     * 32 bits.
                                     */
                                    TWOSCOMPLEMENT {

                                        @Override
                                        int maxAllowedBitwidth() {
                                            return 32;
                                        }

                                        @Override
                                        IntRange range(int bitwidth) {
                                            final int shift = bitwidth - 1;
                                            return Ints.range(-1 << shift, (1 << shift) - 1);
                                        }
                                    };

        /**
         * Returns the maximum bitwidth allowed by this encoding.
         *
         * @return maximum bitwidth allowed by this encoding.
         */
        abstract int maxAllowedBitwidth();

        /**
         * Returns the range of integers representable with this encoding using the
         * given number of bits.
         *
         * @requires bitwidth > 0
         * @return range of integers representable with this encoding using the given
         *         number of bits.
         */
        abstract IntRange range(int bitwidth);
    }

}
