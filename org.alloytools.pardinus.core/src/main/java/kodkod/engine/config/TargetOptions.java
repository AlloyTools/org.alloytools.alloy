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
import kodkod.engine.TargetOrientedSolver;

/**
 * The options required by a {@link TargetOrientedSolver target-oriented solver}
 * for handling target-oriented finding problems. Currently allows this temporal
 * mode to be switched on and sets the execution mode, i.e., whether to find
 * solutions close or far from the target.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 */
public interface TargetOptions extends PardinusOptions {

	/**
	 * Instructs the solver whether to run in target-oriented mode. Will require
	 * an appropriate {@link TargetOrientedSolver solver} that is able to handle
	 * such execution mode. Must be set prior to solver creation in order to
	 * correctly initialize the process.
	 * 
	 * @param run
	 *            whether to run in target-oriented mode.
	 */
	public void setRunTarget(boolean run);

	/**
	 * The target-oriented mode that will be followed by the solver.
	 * 
	 * @return the target-oriented mode followed by the solver.
	 */
	public TMode targetMode();

	/**
	 * Provides the solver with a re-targeting strategy to
	 * apply between instances returned. If null, will apply
	 * Pardinus standard re-targeting.
	 *
	 * @param r retargeting strategy object
	 */
	void setRetargeter(Retargeter r);

	/**
	 * Get the current retargeting strategy
	 * @return the retargeting strategy used by the solver
	 */
	public Retargeter retargeter();

	/**
	 * Instructs the {@link TargetOrientedSolver solver} to solve the problem in
	 * a specific target-oriented mode. This assumes that the target-oriented
	 * constructs were previously initialized.
	 * 
	 * @param mode
	 *            the target-oriented mode to be followed by the solver.
	 */
	public void setTargetMode(TMode mode);

	public enum TMode {
		FAR, CLOSE
	}

}
