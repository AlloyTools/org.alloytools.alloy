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

/**
 * The options required by a {@link DecomposedSolver decomposed solver} for
 * handling model finding problems with a decomposed strategy. Currently allows
 * this temporal mode to be switched on, to specify particular options for the
 * first stage of the process and to configure how the second stage solvers are
 * processed.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 */
public interface DecomposedOptions extends PardinusOptions {

	/**
	 * Instructs the solver whether to run in decomposed mode. Will require an
	 * appropriate {@link DecomposedSolver solver} that is able to handle such
	 * execution mode. Must be set prior to solver creation in order to
	 * correctly initialize the process. A clone of <this> will be used at this
	 * moment for the partial problem options, which can modified independently.
	 * Once this method is called any changes to <this> are no longer propagated
	 * to the partial problem options.
	 * 
	 * @param run
	 *            whether to run in decomposed mode.
	 */
	public void setRunDecomposed(boolean run);

	/**
	 * The decomposed strategy that will be followed by the solver.
	 * 
	 * @return the decomposed strategy followed by the solver.
	 */
	public DMode decomposedMode();

	/**
	 * Instructs the {@link DecomposedSolver solver} to solve the problem with a
	 * specific decomposed strategy. This assumes that the decomposed constructs
	 * were previously initialized.
	 * 
	 * @param mode
	 *            the decomposed strategy to be followed by the solver.
	 */
	public void setDecomposedMode(DMode mode);

	public enum DMode {
		PARALLEL, HYBRID, INCREMENTAL;
	}

	/**
	 * The number of threads that will be used to solve the integrated problems.
	 * If in hybrid mode, one of the threads will be used by the batch problem.
	 * If 1, then will solve the problems sequentially.
	 * 
	 * @return the number of threads for solving integrated problems.
	 */
	public int threads();

	/**
	 * Sets the number of threads that will be used to solve the integrated
	 * problems.
	 * 
	 * @param threads
	 *            the number of threads for solving integrated problems.
	 */
	public void setThreads(int threads);

	/**
	 * The specific options to the partial (configuration) solver. Unless
	 * {@link #setConfigOptions(ExtendedOptions)} is called, a clone of
	 * <this> at the time of activation ({@link #setRunDecomposed(boolean)})
	 * will be used, which can be updated indenpendently.
	 * 
	 * @return the options for the partial solver.
	 */
	public ExtendedOptions configOptions();

	/**
	 * Sets specific options to the partial (configuration) solver. Unless this
	 * method is called, the overall decomposed options at the time of
	 * activation ({@link #setRunDecomposed(boolean)}) are used by the partial
	 * solver.
	 * 
	 * @param opt
	 *            the options for the partial solver.
	 */
	public void setConfigOptions(ExtendedOptions opt);

	// TODO
	public String uniqueName();

	// TODO
	public boolean setUniqueName(String name);

}
