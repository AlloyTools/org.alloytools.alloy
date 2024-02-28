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

import kodkod.engine.Retargeter;

/**
 * Stores information about various user-level translation and analysis options.
 * with support for every Pardinus functionality (temporal, unbounded,
 * decomposed, target-oriented). Inherits from regular Kodkod options bounded
 * configurations.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy, target-oriented,
 *         temporal, unbounded and decomposed model finding
 */
public class ExtendedOptions extends Options implements BoundedOptions,
		DecomposedOptions, TemporalOptions, TargetOptions, UnboundedOptions {

	/**
	 * Constructs an Extended Options object initialized with default values.
	 */
	public ExtendedOptions() {
		super();
	}

	/**
	 * Constructs an Extended Options object by copy.
	 * 
	 * @param options
	 *            the options to be copied.
	 */
	public ExtendedOptions(ExtendedOptions options) {
		super(options);
		this.run_target = options.run_target;
		this.run_decomposed = options.run_decomposed;
		this.run_temporal = options.run_temporal;
		this.threads = options.threads;
		this.target_mode = options.target_mode;
		this.decomp_mode = options.decomp_mode;
		this.config_options = options.config_options!=null?options.config_options.clone():null;
		this.trace_length = options.trace_length;
		this.min_trace_length = options.min_trace_length;
		this.name = options.name;
		this.retargeter = options.retargeter;
	}

	// target-oriented solving

	private boolean run_target = false;
	private TMode target_mode = TMode.CLOSE;
	private Retargeter retargeter = null;
	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean targetoriented() {
		return run_target;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setRunTarget(boolean runTarget) {
		this.run_target = runTarget;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public TMode targetMode() {
		return target_mode;
	}

	@Override
	/**
	 * See {@link Retargeter}.
	 */
	public void setRetargeter(Retargeter r) {
		this.retargeter = r;
	}

	@Override
	public Retargeter retargeter() {
		return retargeter;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setTargetMode(TMode mode) {
		target_mode = mode;
	}

	// decomposed solving
	
	private boolean run_decomposed = false;
	private int threads = 4;
	private DMode decomp_mode = DMode.PARALLEL;
	private ExtendedOptions config_options = null;
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean decomposed() {
		return run_decomposed;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public void setRunDecomposed(boolean runDecomposed) {
		this.run_decomposed = runDecomposed;
		if (config_options != null)
			config_options.setRunDecomposed(runDecomposed);
		else
			config_options = this.clone();
	}
	
	/**
	 * {@inheritDoc}
	 */
	public DMode decomposedMode() {
		return decomp_mode;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public void setDecomposedMode(DMode mode) {
		this.decomp_mode = mode;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public int threads() {
		return threads;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setThreads(int threads) {
		this.threads = threads;
	}

	/**
	 * {@inheritDoc}
	 */
	public ExtendedOptions configOptions() {
		return config_options;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setConfigOptions(ExtendedOptions opt) {
		config_options = opt;
	}

	// temporal solving
	
	private boolean run_temporal = false;
	private int trace_length = 2;
	private int min_trace_length = 1;

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean temporal() {
		return run_temporal;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public void setRunTemporal(boolean runTemporal) {
		this.run_temporal = runTemporal;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public int maxTraceLength() {
		return trace_length;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public int minTraceLength() {
		return min_trace_length;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setMaxTraceLength(int trace_length) {
		this.trace_length = trace_length;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public void setMinTraceLength(int trace_length) {
		this.min_trace_length = trace_length;
	}


	// unbounded solving
	private boolean run_unbounded = false;
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean unbounded() {
		return run_unbounded;
	}

	/**
	 * {@inheritDoc}
	 */
	public void setRunUnbounded(boolean runUnbounded) {
		this.run_unbounded = runUnbounded;
	}

	/**
	 * Returns a shallow copy of this Extended Options object. In particular,
	 * the returned options shares the same {@linkplain #reporter()},
	 * {@linkplain #solver()} factory and partial problem options objects as
	 * this Extended Options.
	 * 
	 * @return a shallow copy of this Extended Options object.
	 */
	public ExtendedOptions clone() {
		final ExtendedOptions c = new ExtendedOptions();
		c.setSolver(solver());
		c.setReporter(reporter());
		c.setBitwidth(bitwidth());
		c.setIntEncoding(intEncoding());
		c.setSharing(sharing());
		c.setSymmetryBreaking(symmetryBreaking());
		c.setSkolemDepth(skolemDepth());
		c.setLogTranslation(logTranslation());
		c.setCoreGranularity(coreGranularity());
		c.setNoOverflow(noOverflow()); // [AM]
		c.run_decomposed = run_decomposed;
		c.run_temporal = run_temporal;
		c.run_target = run_target;
		c.setThreads(threads);
		c.setDecomposedMode(decomp_mode);
		c.setConfigOptions(config_options);
		c.setMaxTraceLength(trace_length);
		c.setMinTraceLength(min_trace_length);
		c.name = name;
		c.setRetargeter(retargeter);
		return c;
	}

	/**
	 * Returns a string representation of this Extended Options object.
	 * @return a string representation of this Extended Options object.
	 */
	public String toString() {
		StringBuilder b = new StringBuilder(super.toString());
		b.append("\n run target: ");
		b.append(run_target);
		b.append("\n target mode: ");
		b.append(target_mode);
		b.append("\n run decomposed: ");
		b.append(run_decomposed);
		b.append("\n decomposed mode: ");
		b.append(decomp_mode);
		b.append("\n threads: ");
		b.append(threads);
		b.append("\n run temporal: ");
		b.append(run_temporal);
		b.append("\n min trace length: ");
		b.append(min_trace_length);
		b.append("\n max trace length: ");
		b.append(trace_length);
		b.append("\n run unbounded: ");
		b.append(run_unbounded);
		b.append("\n custom retargeter?: ");
		b.append(retargeter != null);
		return b.toString();
	}

	private String name;
	
	@Override
	public String uniqueName() {
		if (name == null)
			name = this.hashCode()+"";
		return name;
	}

	@Override
	public boolean setUniqueName(String name) {
		if (this.name != null)
			return false;
		this.name = name;
		return true;
	}



}
