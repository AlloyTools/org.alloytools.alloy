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

import java.util.AbstractMap;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.decomp.DMonitor;
import kodkod.engine.decomp.DProblem;
import kodkod.instance.PardinusBounds;

/**
 * An executor that effectively handles a decomposed model finding problem
 * problem, defined by a pair of bounds, a pair of formulas and the solver that
 * will be launched in parallel. It is also defined by the number of threads
 * that will be launched.
 * 
 * While the partial problem is expected to be solved by a Kodkod solver
 * (iteration, symmetry breaking), the integrated problem may be tackled by
 * different (possibly unbounded) solvers.
 * 
 * @param <S>
 *            The solver that will be used to handle integrated problems.
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
abstract public class DProblemExecutor<S extends AbstractSolver<PardinusBounds, ExtendedOptions>>
		extends Thread {

	/** the decomposed problem bounds */
	public final PardinusBounds bounds;

	/** the decomposed problem formulas */
	public final Formula formula;

	/** the underlying solvers */
	public final ExtendedSolver solver_partial;
	public final S solver_integrated;

	/**
	 * the executor managing the launching of the threads
	 * 
	 * TODO: replace by new ThreadPoolExecutor(corePoolSize, maximumPoolSize,
	 * keepAliveTime, unit, workQueue) to manage LIFO
	 */
	public final ExecutorService executor;

	/** a reporter that monitors the solving process */
	public final DMonitor monitor;

	/**
	 * Constructs an effective decomposed problem executor for a decomposed
	 * model finding problem and the number of desired parallel solvers.
	 * 
	 * The formula and bounds will only be decomposed by a slicer further down
	 * the process.
	 * 
	 * TODO: allow the slicer to be parameterized.
	 * 
	 * @param rep
	 *            a monitor for the decomposed process.
	 * @param formula
	 *            the formula to be solved.
	 * @param bounds
	 *            the bounds of the problem.
	 * @param solver1
	 *            the solver for the partial problem.
	 * @param solver2
	 *            the solver for the integrated problem.
	 * @param n
	 *            the number of solver threads.
	 */
	DProblemExecutor(DMonitor rep, Formula formula, PardinusBounds bounds, 
			ExtendedSolver solver1, S solver2, int n) {
		this.formula = formula;
		this.bounds = bounds;
		this.solver_partial = solver1;
		this.solver_integrated = solver2;
		this.executor = Executors.newFixedThreadPool(n);
		this.monitor = rep;
	}

	/**
	 * Called by one of the parallel integrated model finders when finished
	 * solving.
	 * 
	 * @param sol
	 *            the solution calculated by the caller.
	 */
	public abstract void end(DProblem<S> sol);

	/**
	 * TODO
	 * @param e
	 */
	public abstract void failed(Throwable e);

	/**
	 * Starts the solving process.
	 */
	public abstract void run();

	/**
	 * Calculates the next batch of solution. May block until a solution is calculated by
	 * an integrated problem.
	 * 
	 * @return the solution found.
	 * @throws InterruptedException
	 *             if interrupted while waiting.
	 */
	public abstract Entry<Solution, Iterator<Solution>> next() throws InterruptedException;

	/**
	 * Tests whether there are further solutions. May block if there is no
	 * solution in the queue and there are still running integrated problems.
	 * 
	 * @return whether there are further solutions.
	 * @throws InterruptedException
	 *             if interrupted while waiting.
	 */
	public abstract boolean hasNext() throws InterruptedException;

	/**
	 * Terminates the thread executor and the running solvers.
	 * 
	 * @throws InterruptedException
	 *             if interrupted while waiting.
	 */
	public void terminate() throws InterruptedException {
		if (!executor.isShutdown())
			executor.shutdownNow();
		if (!executor.isTerminated()) {
			boolean timeout = executor.awaitTermination(0, TimeUnit.HOURS);
			monitor.terminated(timeout);
		}
	}
	
	static Entry<Solution,Iterator<Solution>> poison(Solution s) {
		if (s == null)
			s = Solution.unsatisfiable(new Statistics(-1,-1,-1,-1,-1),null);
		return new AbstractMap.SimpleEntry<Solution, Iterator<Solution>>(s,new Explorer<Solution>() {
			
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public Solution next() {
				throw new NoSuchElementException();
			}

			@Override
			public Solution nextC() {
				throw new NoSuchElementException();
			}

			@Override
			public Solution nextP() {
				throw new NoSuchElementException();
			}

			@Override
			public Solution nextS(int state, int delta, Set<Relation> change) {
				throw new NoSuchElementException();
			}

			@Override
			public boolean hasNextP() {
				return false;
			}

			@Override
			public boolean hasNextC() {
				return false;
			}
		});
	}
	
	static boolean isPoison(Solution sol) {
		return sol.stats().primaryVariables() == -1;
	}
}