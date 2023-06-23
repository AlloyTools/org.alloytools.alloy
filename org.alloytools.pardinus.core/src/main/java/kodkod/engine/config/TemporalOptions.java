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

import kodkod.engine.TemporalSolver;
import kodkod.engine.UnboundedSolver;

/**
 * The options required by a {@link TemporalSolver temporal solver} for handling
 * temporal model finding problems. Currently allows this temporal mode to be
 * switched on and sets a maximum trace to be analyzed.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 */
public interface TemporalOptions extends PardinusOptions {

	/**
	 * Instructs the solver whether to run in temporal mode. Will require an
	 * appropriate {@link TemporalSolver solver} that is able to handle such
	 * execution mode. Must be set prior to solver creation in order to
	 * correctly initialize the process.
	 * 
	 * TODO: is this needed? there is no way to ignore temporal formulas
	 * 
	 * @param run
	 *            whether to run in temporal mode.
	 */
	public void setRunTemporal(boolean run);

	/**
	 * The maximum trace length that will be explored by the temporal model
	 * finder. {@link UnboundedSolver unbounded temporal solvers} will ignore
	 * this value.
	 * 
	 * @return the maximum trace length.
	 */
	public int maxTraceLength();

	public int minTraceLength();

	/**
	 * Updates the maximum trace length that will be explored by the temporal
	 * model finder. {@link UnboundedSolver unbounded temporal solvers} will
	 * ignore this value.
	 * 
	 * @param traceLength
	 *            the new maximum trace length.
	 */
	public void setMaxTraceLength(int traceLength);
	
	public void setMinTraceLength(int traceLength);


}
