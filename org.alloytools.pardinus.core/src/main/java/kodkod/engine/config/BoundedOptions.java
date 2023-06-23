/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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

import kodkod.engine.config.Options.IntEncoding;
import kodkod.engine.satlab.SATFactory;

/**
 * The options required by a bounded model finding problem. These rely on SAT
 * solvers to solver the problems.
 * 
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] model finding hierarchy
 */
//[HASLab] model finding hierarchy
public interface BoundedOptions extends PardinusOptions {

	/**
	 * Returns a primitive solver factory used to generate
	 * {@link kodkod.engine.PrimitiveSolver primitive solvers}.
	 * 
	 * @return a primitive solver factory
	 */
	public SATFactory solver();

	/**
	 * Sets the primitive solver factory used to generate
	 * {@link kodkod.engine.PrimitiveSolver primitive solvers}.
	 * 
	 * @param solver the primitive solver factory
	 */
	public void setSolver(SATFactory solver);
	
	/**
	 * Returns the size of the integer representation. For example, if
	 * this.intEncoding is BINARY and this.bitwidth = 5 (the default), then all
	 * operations will yield one of the five-bit numbers in the range [-16..15].
	 * If this.intEncoding is UNARY and this.bitwidth = 5, then all operations
	 * will yield one of the numbers in the range [0..5].
	 */
	public int bitwidth();

	/** Sets this.bitwidth to the given value. */
	public void setBitwidth(int bitwidth);

	/** Returns the noOverflow flag. */
	public boolean noOverflow();

	/** Sets the noOverflow flag. */
	public void setNoOverflow(boolean noOverflow);

	/**
	 * Returns the 'amount' of symmetry breaking to perform. If a non-symmetric
	 * solver is chosen for this.solver, this value controls the maximum length
	 * of the generated lex-leader symmetry breaking predicate. In general, the
	 * higher this value, the more symmetries will be broken. But setting the
	 * value too high may have the opposite effect and slow down the solving.
	 * The default value for this property is 20.
	 */
	public int symmetryBreaking();

	/** Sets the symmetryBreaking option to the given value. */
	public void setSymmetryBreaking(int symmetryBreaking);

	/**
	 * Returns the depth to which existential quantifiers are skolemized. A
	 * negative depth means that no skolemization is performed. The default
	 * depth of 0 means that only existentials that are not nested within a
	 * universal quantifiers are skolemized. A depth of 1 means that
	 * existentials nested within a single universal are also skolemized, etc.
	 */
	public int skolemDepth();

	public void setSkolemDepth(int skolemDepth);

	/**
	 * Returns the integer encoding that will be used for translating
	 * {@link kodkod.ast.IntExpression int nodes}. The default is BINARY
	 * representation, which allows negative numbers. UNARY representation is
	 * best suited to problems with small scopes, in which cardinalities are
	 * only compared (and possibly added to each other or non-negative numbers).
	 */
	public IntEncoding intEncoding();

	/** Sets the intEncoding option to the given value. */
	public void setIntEncoding(IntEncoding encoding);

	/**
	 * Returns the translation logging level (0, 1, or 2), where 0 means logging
	 * is not performed, 1 means only the translations of top level formulas are
	 * logged, and 2 means all formula translations are logged. This is
	 * necessary for determining which formulas occur in the unsat core of an
	 * unsatisfiable formula. Logging is off by default, since it incurs a
	 * non-trivial time overhead.
	 */
	public int logTranslation();

	/** Sets the translation logging level. */
	public void setLogTranslation(int logTranslation);

	/**
	 * Returns the core granularity level. The default is 0, which means that
	 * top-level conjuncts of the input formula are used as "roots" for the
	 * purposes of core minimization and extraction. Granularity of 1 means that
	 * the top-level conjuncts of the input formula's negation normal form (NNF)
	 * are used as roots; granularity of 2 means that the top-level conjuncts of
	 * the formula's skolemized NNF (SNNF) are used as roots; and, finally, a
	 * granularity of 3 means that the universal quantifiers of the formula's
	 * SNNF are broken up and that the resulting top-level conjuncts are then
	 * used as roots for core minimization and extraction.
	 * 
	 * <p>
	 * Note that the finer granularity (that is, a larger value of
	 * this.coreGranularity) will provide better information at the cost of
	 * slower core extraction and, in particular, minimization.
	 * </p>
	 */
	public int coreGranularity();

	/** Sets the core granularity level. */
	public void setCoreGranularity(int coreGranularity);

}
