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

import kodkod.engine.DecomposedSolver;
import kodkod.engine.TargetOrientedSolver;
import kodkod.engine.TemporalSolver;
import kodkod.engine.UnboundedSolver;

/**
 * The fundamental options required by every model finding problem supported by
 * Kodkod and the Pardinus extensions. Specifies reporters and which execution
 * modes are to be followed by the solvers.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 */
public interface PardinusOptions {

	/**
	 * Returns a reporter.
	 * 
	 * @return a reporter
	 */
	public Reporter reporter();

	/**
	 * Sets the reporter.
	 * 
	 * @param reporter
	 *            a reporter.
	 */
	public void setReporter(Reporter reporter);

	/**
	 * Whether the solver should run in decomposed mode. Will require an
	 * appropriate {@link DecomposedSolver solver} that is able to handle such
	 * execution mode. If false will run in an amalgamated strategy.
	 * 
	 * @return whether to run in decomposed mode.
	 */
	public boolean decomposed();

	/**
	 * Whether the solver should run in temporal mode. Will require an
	 * appropriate {@link TemporalSolver solver} that is able to handle such
	 * execution mode. If false, temporal formulas will throw an error.
	 * 
	 * TODO: is this needed? there is no way to ignore temporal formulas
	 * 
	 * @return whether to run in temporal mode.
	 */
	@Deprecated
	public boolean temporal();
	
	/**
	 * Whether the solver should run in unbounded mode. Will require an
	 * appropriate {@link UnboundedSolver solver} that is able to handle such
	 * execution mode. Will be ignored if {@link #temporal()} false.
	 * 
	 * @return whether to run in unbounded mode.
	 */
	public boolean unbounded();

	/**
	 * Whether the solver should run in target-oriented mode. Will require an
	 * appropriate {@link TargetOrientedSolver solver} that is able to handle such
	 * execution mode. If false, targets will be ignored even if specified.
	 * 
	 * @return whether to run in target-oriented mode.
	 */
	public boolean targetoriented();

}
