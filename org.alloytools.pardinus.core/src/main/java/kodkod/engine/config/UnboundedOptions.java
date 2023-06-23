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

import kodkod.engine.UnboundedSolver;

/**
 * The options required by an {@link UnboundedSolver unbounded solver} for
 * handling unbounded temporal model finding problems. Currently just allows
 * this unbounded mode to be switched on.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 */
public interface UnboundedOptions extends TemporalOptions {

	/**
	 * Instructs the solver whether to run in unbounded mode. Will require an
	 * appropriate {@link UnboundedSolver solver} that is able to handle such
	 * execution mode. Must be set prior to solver creation in order to
	 * correctly initialize the process.
	 * 
	 * 
	 * @param run
	 *            whether to run in unbounded mode.
	 */
	public void setRunUnbounded(boolean run);

}
