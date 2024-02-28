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

import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.DecomposedOptions;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.PardinusOptions;
import kodkod.engine.config.Reporter;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;

/**
 * A computational engine for solving relational satisfiability problems in a
 * decomposed strategy. Such a problem is described by a
 * {@link kodkod.ast.Formula formula} in first order relational logic; finite
 * {@link ExtendedOptions bounds} on the value of each {@link Relation
 * relation} constrained by the formula that have been split into two sets; and
 * a set of {@link PardinusOptions options} specifying, among other global
 * parameters, which solver should be used in the second stage of the process. A
 * different set of options can be used to control the regular {@link Solver
 * Kodkod solver} used in the first stage.
 * 
 * <p>
 * A {@link DecomposedPardinusSolver} takes as input a relational problem and
 * produces a satisfying model or an {@link Instance instance} of it, if one
 * exists. The current process solves each of the second stage problems in
 * parallel, and support a hybrid mode that keeps an amalgamated problem running
 * in background.
 * </p>
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 *
 */
public class DecomposedPardinusSolver<S extends AbstractSolver<PardinusBounds, ExtendedOptions>> implements
		DecomposedSolver<ExtendedOptions>, ExplorableSolver<PardinusBounds, ExtendedOptions> {

	/** the regular Kodkod solver used in the parallelization */
	final private ExtendedSolver solver1;
	final private S solver2;

	/** a manager for the decomposed solving process */
	private DProblemExecutor<S> executor;

	/** the decomposed problem options */
	final private ExtendedOptions options;
	
	/**
	 * Constructs a new decomposed solver built over a standard Kodkod
	 * {@link kodkod.engine.Solver solver}. The solving
	 * {@link kodkod.engine.config.Options options} are retrieved from the
	 * regular solver.
	 * 
	 * @param solver
	 *            the regular solver over which the decomposed solver is built.
	 * @throws IllegalArgumentException
	 *             if the solver is not incremental.
	 */
	public DecomposedPardinusSolver(ExtendedOptions options, S solver) {
		this.options = options;
		this.solver1 = new ExtendedSolver(options.configOptions());
		this.solver2 = solver;
	}

	/**
	 * Solves a decomposed model finding problem, comprised by a pair of
	 * {@link kodkod.ast.Formula formulas} and a pair of
	 * {@link kodkod.instance.Bounds bounds}. Essentially launches an
	 * {@link kodkod.engine.DProblemExecutor executor} to handle the
	 * decomposed problem in parallel, given the defined
	 * {@link kodkod.pardinus.decomp.DOptions options}.
	 * @param f1
	 *            the partial problem formula.
	 * @param f2
	 *            the remainder problem formula.
	 * @param b1
	 *            the partial problem bounds.
	 * @param b2
	 *            the remainder problem bounds.
	 * 
	 * @requires f1 to be defined over b1 and f2 over b2.
	 * @return a decomposed solution.
	 * @throws InterruptedException
	 *             if the solving process is interrupted.
	 */
	@Override
	public Solution solve(Formula formula, PardinusBounds bounds) {
		if (!options.configOptions().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");

		executor = new DProblemExecutorImpl<S>(options.reporter(), formula, bounds, solver1, solver2, options.threads(), options.decomposedMode() == DMode.HYBRID);
		ExecutorService ex = Executors.newSingleThreadExecutor();
		Future<?> fut = ex.submit(executor);
		try {
			fut.get();
		} catch (InterruptedException | ExecutionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Solution sol = null;
		try {
			Entry<Solution,Iterator<Solution>> exp = executor.next();
			sol = exp.getKey();
			executor.terminate();
		} catch (InterruptedException e) {
			options.reporter().debug("Waiting for next interrupted.");
			try {
				executor.terminate();
			} catch (InterruptedException e1) {
				e1.printStackTrace();
			}
//			e.printStackTrace();
		}
		return sol;
	}

	/**
	 * Retrieves the decomposed problem executor that handled the decomposed problem.
	 * 
	 * @return the decomposed problem executor that solved the problem.
	 */
	public DProblemExecutor<S> executor() {
		return executor;
	}

	/**
	 * Releases the resources, if any.
	 */
	public void free() {
		solver1.free();
		solver2.free();
	}

	@Override
	public ExtendedOptions options() {
		return options;
	}

	@Override
	public Explorer<Solution> solveAll(Formula formula, PardinusBounds bounds) {
		if (!options.configOptions().solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");
		return new DSolutionIterator<S>(formula, bounds, options, solver1, solver2); 
	}
	
	private static class DSolutionIterator<S extends AbstractSolver<PardinusBounds, ExtendedOptions>> implements Explorer<Solution> {
		private DProblemExecutor<S> executor;
		private Reporter reporter;
		private Iterator<Solution> sols;
		
		/**
		 * Constructs a solution iterator for the given formula, bounds, and options.
		 */
		DSolutionIterator(Formula formula, PardinusBounds bounds, DecomposedOptions options, ExtendedSolver solver1, S solver2) {
			reporter = options.reporter();
			if (options.decomposedMode() == DMode.HYBRID)
				executor = new DProblemExecutorImpl<S>(options.reporter(), formula, bounds, solver1, solver2, options.threads(), true);
			else
				executor = new DProblemExecutorImpl<S>(options.reporter(), formula, bounds, solver1, solver2, options.threads(), false);
			ExecutorService ex = Executors.newSingleThreadExecutor();
			Future<?> fut = ex.submit(executor);
			try {
				fut.get();
			} catch (InterruptedException | ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		/**
		 * Returns true if there is another solution.
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			if (sols == null) return hasNextC();
			return sols.hasNext();
		}
		
		/**
		 * Returns the next solution if any.
		 * @see java.util.Iterator#next()
		 */
		@Override
		public Solution nextP() {
			if  (! (sols instanceof Explorer<?>)) 
				throw new UnsupportedOperationException();
			if (!hasNextP()) return null;
			if (sols == null) return nextC();
			return ((Explorer<Solution>) sols).nextP();
		}
		
		@Override
		public Solution nextS(int state, int delta, Set<Relation> changes) {
			if  (! (sols instanceof Explorer<?>)) 
				throw new UnsupportedOperationException();
			if (!hasNextP()) return null;
			return ((Explorer<Solution>) sols).nextS(state, delta, changes);
		}
		
		@Override
		public Solution nextC() {
			if (!hasNextC()) return null;
			try {
				Entry<Solution,Iterator<Solution>> xx = executor.next();
				Solution sol = xx.getKey();
				sols = xx.getValue();
				return sol;
			} catch (InterruptedException e) {
				reporter.debug("Waiting for next interrupted.");
				try {
					executor.terminate();
				} catch (InterruptedException e1) {
					e1.printStackTrace();
				}
				// Should throw AbortedException
				e.printStackTrace();
			}
			return null;
		}

		/** @throws UnsupportedOperationException */
		public void remove() { throw new UnsupportedOperationException(); }

		@Override
		public Solution next() {
			if (!hasNext()) return null;
			if (sols == null) return nextC();
			return sols.next();
		}

		@Override
		public boolean hasNextP() {
			if  (! (sols instanceof Explorer<?>)) 
				throw new UnsupportedOperationException();
			if (sols == null) return hasNextC();
			return ((Explorer<Solution>) sols).hasNextP();
		}

		@Override
		public boolean hasNextC() {
			try {				
				return executor.hasNext();
			} catch (InterruptedException e) {
				reporter.debug("Waiting for next interrupted.");
				try {
					executor.terminate();
				} catch (InterruptedException e1) {
					e1.printStackTrace();
				}
				// Should throw AbortedException
//				e.printStackTrace();
			}
			return false;
		}

	}
	

}
