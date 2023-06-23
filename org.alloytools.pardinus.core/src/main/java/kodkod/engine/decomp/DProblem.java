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

import java.util.AbstractMap;
import java.util.Iterator;
import java.util.Map.Entry;

import kodkod.ast.Formula;
import kodkod.engine.DProblemExecutor;
import kodkod.engine.Explorer;
import kodkod.engine.IterableSolver;
import kodkod.engine.AbstractSolver;
import kodkod.engine.Solution;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.PardinusBounds;

/**
 * A problem thread that is to be run in a decomposed model finding procedure.
 * 
 * @param <S>
 *            The solver that will be used to handle integrated problems.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class DProblem<S extends AbstractSolver<PardinusBounds,ExtendedOptions>>
		extends Thread {

	private final S solver;

	private Iterator<Solution> solutions;
	private Solution solution;
	protected final PardinusBounds bounds;
	private final Formula formula;
	protected final DProblemExecutor<S> manager;

	/**
	 * Constructs a new problem thread, that will callback the decomposed model
	 * solving manager. Retrieves the problem from the manager.
	 * 
	 * @param manager
	 *            the callback manager.
	 */
	public DProblem(DProblemExecutor<S> manager) {
		this(manager,manager.formula,manager.bounds.amalgamated());
		assert bounds.amalgamated() == null;
	}

	
	/**
	 * Constructs a new problem thread, that will callback the decomposed model
	 * solving manager.
	 * 
	 * @param manager
	 *            the callback manager.
	 * @param formula
	 *            the formula of the problem.
	 * @param bounds
	 *            the bounds of the problem.
	 */
	protected DProblem(DProblemExecutor<S> manager, Formula formula,
			PardinusBounds bounds) {
//		assert bounds.resolved();
		this.manager = manager;
		this.solver = manager.solver_integrated;
		this.bounds = bounds;
		this.formula = formula;
	}

	public void run() {
		try {
			if (solver instanceof IterableSolver<?, ?>) {
				if (solutions == null) {
					solutions = ((IterableSolver) solver).solveAll(formula, bounds);
					solution = solutions.next();
					solver.free();
				}
			} else {
				solution = ((AbstractSolver) solver).solve(formula, bounds);
				solver.free();
			}
			manager.end(this);
		} catch (Exception e) {
			manager.failed(e);
		}
	}
	
	public Entry<Solution,Iterator<Solution>> getSolutions() {
		return new AbstractMap.SimpleEntry(solution,solutions);
	}


	
	
	
	
}