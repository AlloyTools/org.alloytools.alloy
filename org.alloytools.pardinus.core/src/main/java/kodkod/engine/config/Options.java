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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
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
 * @specfield logTranslation: [0..2] // log translation events, default is 0 (no
 *            logging)
 * @specfield coreGranularity: [0..3] // unsat core granularity, default is 0
 *            (only top-level conjuncts are considered)
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] model finding hierarchy
 */
// [HASLab] model finding hierarchy, copy constructor
public class Options implements Cloneable, BoundedOptions { 
	private Reporter reporter = new AbstractReporter(){};
	private SATFactory solver = SATFactory.DefaultSAT4J;
	private int symmetryBreaking = 20;
	private IntEncoding intEncoding = IntEncoding.TWOSCOMPLEMENT;
	private int bitwidth = 4;
	private int sharing = 3;
	private boolean noOverflow = false; // [AM]
	private int skolemDepth = 0;
	private int logTranslation = 0;
	private int coreGranularity = 0;

	//[AM]
	public static boolean isDebug() {
	    // [HASLab]
		return System.getProperty("debug","no").equals("yes");
//		return true; //TODO: read from the environment or something
	}
	
	/**
	 * Constructs an Options object initialized with default values.
	 * @ensures this.solver' = SATFactory.DefaultSAT4J
	 *          this.reporter' is silent (no messages reported)
	 *          this.symmetryBreaking' = 20
	 *          this.sharing' = 3
	 *          this.intEncoding' = BINARY
	 *          this.bitwidth' = 4
	 *          this.skolemDepth' = 0
	 *          this.logTranslation' = 0
	 *          this.coreGranularity' = 0
	 */
	public Options() {}
	
	/**
	 * Constructs an Options object by copy.
	 * @param options the options to be copied.
	 */
	// [HASLab]
	public Options(Options options) {
		this.setSolver(options.solver());
		this.setReporter(options.reporter());
		this.setBitwidth(options.bitwidth());
		this.setIntEncoding(options.intEncoding());
		this.setSharing(options.sharing());
		this.setSymmetryBreaking(options.symmetryBreaking());
		this.setSkolemDepth(options.skolemDepth());
		this.setLogTranslation(options.logTranslation());
		this.setCoreGranularity(options.coreGranularity());		
	}
	
	/**
	 * {@inheritDoc}
	 * The default is SATSolver.DefaultSAT4J.
	 * @return this.solver
	 */
	public SATFactory solver() {
		return solver;
	}
	
	/**
	 * {@inheritDoc}
	 * @ensures this.solver' = solver
	 * @throws NullPointerException  solver = null
	 */
	public void setSolver(SATFactory solver) {
		if (solver==null)
			throw new NullPointerException();
		this.solver = solver;
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.reporter
	 */
	public Reporter reporter() {
		return reporter;
	}
	
	/**
	 * {@inheritDoc}
	 * @requires reporter != null
	 * @ensures this.reporter' = reporter
	 * @throws NullPointerException  reporter = null
	 */
	public void setReporter(Reporter reporter) {
		if (reporter==null)
			throw new NullPointerException();
		this.reporter = reporter;
	}
		

	/** {@inheritDoc} */ 
	// [AM]
	public boolean noOverflow()                   { return noOverflow; }
	/** {@inheritDoc} */ 
	// [AM]	
	public void setNoOverflow(boolean noOverflow) { this.noOverflow = noOverflow; }

	
	/**
	 * @throws IllegalArgumentException  arg !in [min..max]
	 */
	private void checkRange(int arg, int min, int max) {
		if (arg < min || arg > max)
			throw new IllegalArgumentException(arg + " !in [" + min + ".." + max + "]");
	}
	

	
	/**
	 * {@inheritDoc}
	 * @return this.intEncoding
	 */
	public IntEncoding intEncoding() { 
		return intEncoding;
	}
	
	/**
	 * {@inheritDoc}
	 * @ensures this.intEncoding' = encoding
	 * @throws NullPointerException  encoding = null
	 * @throws IllegalArgumentException  this.bitwidth is not a valid bitwidth for the specified encoding
	 */
	public void setIntEncoding(IntEncoding encoding) {
		if (encoding.maxAllowedBitwidth()<bitwidth) throw new IllegalArgumentException();
		this.intEncoding = encoding;
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.bitwidth
	 */
	public int bitwidth() {
		return bitwidth;
	}
	
	/**
	 * {@inheritDoc}
	 * @ensures this.bitwidth' = bitwidth
	 * @throws IllegalArgumentException  bitwidth < 1
	 * @throws IllegalArgumentException  this.intEncoding==BINARY && bitwidth > 32
	 */
	public void setBitwidth(int bitwidth) {
		checkRange(bitwidth, 1, intEncoding.maxAllowedBitwidth());
		this.bitwidth = bitwidth;
	}
	
	/**
	 * Returns the range of integers that can be encoded 
	 * using this.intEncoding and this.bitwidth. 
	 * @return  range of integers that can be encoded 
	 * using this.intEncoding and this.bitwidth. 
	 */
	public IntRange integers() {
		return intEncoding.range(bitwidth);
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.symmetryBreaking
	 */
	public int symmetryBreaking() {
		return symmetryBreaking;
	}
	
	/**
	 * {@inheritDoc}
	 * @ensures this.symmetryBreaking' = symmetryBreaking
	 * @throws IllegalArgumentException  symmetryBreaking !in [0..Integer.MAX_VALUE]
	 */
	public void setSymmetryBreaking(int symmetryBreaking) {
		checkRange(symmetryBreaking, 0, Integer.MAX_VALUE);
		this.symmetryBreaking = symmetryBreaking;
	}
	
	/**
	 * Returns the depth to which circuits are checked for equivalence during translation.
	 * The default depth is 3, and the minimum allowed depth is 1.  Increasing the sharing
	 * may result in a smaller CNF, but at the cost of slower translation times.
	 * @return this.sharing
	 */
	public int sharing() {
		return sharing;
	}
	
	/**
	 * Sets the sharing option to the given value.
	 * @ensures this.sharing' = sharing
	 * @throws IllegalArgumentException  sharing !in [1..Integer.MAX_VALUE]
	 */
	public void setSharing(int sharing) {
		checkRange(sharing, 1, Integer.MAX_VALUE);
		this.sharing = sharing;
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.skolemDepth
	 */
	public int skolemDepth() {
		return skolemDepth;
	}
	
	/**
	 * {@inheritDoc}
	 * Sets the skolemDepth to the given value. 
	 * @ensures this.skolemDepth' = skolemDepth
	 */
	public void setSkolemDepth(int skolemDepth) {
		this.skolemDepth = skolemDepth;
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.logTranslation
	 */
	public int logTranslation() {
		return logTranslation;
	}
	
	/**
	 * {@inheritDoc}
	 * @requires logTranslation in [0..2]
	 * @ensures this.logTranslation' = logTranslation  
	 * @throws IllegalArgumentException  logTranslation !in [0..2]
	 */
	public void setLogTranslation(int logTranslation) {
		checkRange(logTranslation, 0, 2);
		this.logTranslation = logTranslation;
	}
	
	/**
	 * {@inheritDoc}
	 * @return this.coreGranularity
	 */
	public int coreGranularity() { 
		return coreGranularity;
	}
	
	/**
	 * {@inheritDoc}
	 * @requires coreGranularity in [0..3]
	 * @ensures this.coreGranularity' = coreGranularity  
	 * @throws IllegalArgumentException  coreGranularity !in [0..3]
	 */
	public void setCoreGranularity(int coreGranularity) { 
		checkRange(coreGranularity, 0, 3);
		this.coreGranularity = coreGranularity;
	}
	
	/**
	 * Returns a shallow copy of this Options object.  In particular, 
	 * the returned options shares the same {@linkplain #reporter()} 
	 * and {@linkplain #solver()} factory objects as this Options. 
	 * @return a shallow copy of this Options object.
	 */
	public Options clone() {
		final Options c = new Options();
		c.setSolver(solver);
		c.setReporter(reporter);
		c.setBitwidth(bitwidth);
		c.setIntEncoding(intEncoding);
		c.setSharing(sharing);
		c.setSharing(sharing);
		c.setSymmetryBreaking(symmetryBreaking);
		c.setSkolemDepth(skolemDepth);
		c.setLogTranslation(logTranslation);
		c.setCoreGranularity(coreGranularity);
		c.setNoOverflow(noOverflow); // [AM]
		return c;
	}
	
	/**
	 * Returns a string representation of this Options object.
	 * @return a string representation of this Options object.
	 */
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
		b.append("\n noOverflow: "); // [AM]
        b.append(noOverflow);
        return b.toString();
	}
	
	/**
	 * Integer encoding options for the translation of 
	 * {@link kodkod.ast.IntExpression int expressions}.
	 */
	public static enum IntEncoding {
		/**
		 * Two's-complement encoding of integers supports
		 * comparisons, addition, subtraction, multiplication,
		 * division, and all low-level bit operations 
		 * (shifting, and, or, not, etc.).  Maximum allowed
		 * bitwidth for this encoding is 32 bits.
		 */
		TWOSCOMPLEMENT {
			@Override
			int maxAllowedBitwidth() { return 32; }
			@Override
			IntRange range(int bitwidth) { 
				final int shift = bitwidth-1;
				return Ints.range(-1<<shift, (1<<shift)-1);
			}
		};
		
		/**
		 * Returns the maximum bitwidth allowed by this encoding.
		 * @return maximum bitwidth allowed by this encoding.
		 */
		abstract int maxAllowedBitwidth();
		
		/**
		 * Returns the range of integers representable with 
		 * this encoding using the given number of bits.
		 * @requires bitwidth > 0
		 * @return range of integers representable with 
		 * this encoding using the given number of bits.
		 */
		abstract IntRange range(int bitwidth) ;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * Always false as these options are meant for regular Kodkod solvers.
	 */
	// [HASLab] 
	public boolean decomposed() { return false; }

	/**
	 * {@inheritDoc}
	 * 
	 * Always false as these options are meant for regular Kodkod solvers.
	 */
	// [HASLab] 
	public boolean temporal() { return false; }

	/**
	 * {@inheritDoc}
	 * 
	 * Always false as these options are meant for regular Kodkod solvers.
	 */
	// [HASLab] 
	public boolean unbounded() { return false; }
	
	/**
	 * {@inheritDoc}
	 * 
	 * Always false as these options are meant for regular Kodkod solvers.
	 */
	// [HASLab] 
	public boolean targetoriented() { return false; }
	
}
