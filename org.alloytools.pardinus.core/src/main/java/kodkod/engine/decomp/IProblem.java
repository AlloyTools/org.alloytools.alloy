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
package kodkod.engine.decomp;

import kodkod.engine.AbstractSolver;
import kodkod.engine.DProblemExecutor;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.PardinusBounds;

/**
 * A problem thread that represents an integrated problem. The main difference
 * is that a configuration is now registered.
 * 
 * @param <S>
 *            The solver that will be used to handle integrated problems.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
public class IProblem<S extends AbstractSolver<PardinusBounds, ExtendedOptions>>
		extends DProblem<S> {

	@SuppressWarnings("unused")
	private final Solution config;

	/**
	 * Constructs a new integrated problem thread with a given partial solution
	 * (configuration). Retrieves the integrated problem from the manager.
	 * 
	 * @param config
	 *            the partial solution to be extended.
	 * @param manager
	 *            the callback manager.
	 */
	public IProblem(Solution config, DProblemExecutor<S> manager) {
		super(manager, manager.formula, manager.bounds.integrated(config));
		this.config = config;
		assert bounds.amalgamated() != null;
	}

}