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
package kodkod.engine;

import kodkod.ast.Formula;
import kodkod.engine.config.UnboundedOptions;
import kodkod.engine.unbounded.InvalidUnboundedProblem;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.PardinusBounds;

/**
 * An interface for unbounded relational constraint solvers. Pardinus
 * {@link bounds PardinusBounds} are expected, as these contain information
 * regarding unbounded problems. Options are required to specify unbounded
 * configurations.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 *
 * @param <O>
 *            the class of options required by a concrete solver, which should
 *            at least consider unbounded configurations
 *
 */
public interface UnboundedSolver<O extends UnboundedOptions> extends
		TemporalSolver<O> {

	/**
	 * {@inheritDoc}
	 * 
	 * @throws InvalidUnboundedProblem
	 *             if the problem is not supported by the unbounded solver.
	 * @throws InvalidUnboundedSolution
	 *             if the solver's output failed to be parsed.
	 * @throws AbortedException
	 *             if the solving process aborted.
	 */
	@Override
	public Solution solve(Formula formula, PardinusBounds bounds)
			throws InvalidUnboundedProblem, InvalidUnboundedSolution,
			AbortedException;

}
