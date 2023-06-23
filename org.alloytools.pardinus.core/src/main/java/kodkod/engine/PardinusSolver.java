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

import java.io.File;
import java.util.Iterator;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.instance.PardinusBounds;

/**
 * The main Pardinus solver. Depending on the define {@link options
 * MainPardinusOptions}, will choose the appropriate concrete solver, that can
 * be decomposed, bounded or unbounded, temporal, target-oriented or have
 * symbolic bounds.
 * 
 * @author Nuno Macedo // [HASLab] decomposed, unbounded, temporal,
 *         target-oriented, symbolic model finding
 */
public class PardinusSolver implements
		SymbolicSolver<ExtendedOptions>,
		TargetOrientedSolver<ExtendedOptions>,
		DecomposedSolver<ExtendedOptions>,
		TemporalSolver<ExtendedOptions>,
		BoundedSolver<PardinusBounds, ExtendedOptions>,
		UnboundedSolver<ExtendedOptions> {

	private final ExtendedOptions options;
	public final AbstractSolver<PardinusBounds,ExtendedOptions> solver;

	/**
	 * Constructs a new Pardinus solver with the given options. The options are
	 * used to select the appropriate solver, so the execution mode should be
	 * set before calling.
	 * 
	 * The internal solver may be a regular {@link Solver regular Kodkod solver}
	 * , a {@link DecomposedPardinusSolver decomposed Pardinus solver}, a
	 * {@link TemporalPardinusSolver temporal Pardinus solver} or an
	 * {@link ElectrodSolver Electrod solver}. The decomposed solver will use a
	 * regular Kodkod solver for the partial problem and a temporal Pardinus
	 * solver or an Electrod solver for the remainder.
	 * 
	 * @ensures this.options' = options
	 * @throws NullPointerException
	 *             options = null
	 * @throws UnsupportedOperationException
	 *             !options.temporal() && options.unbounded()
	 */
	public PardinusSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();
		
		if (!options.temporal() && options.unbounded())
			throw new IllegalArgumentException("Unbounded solver only for temporal problems.");
		
		if (options.targetoriented() && !options.solver().maxsat())
			throw new IllegalArgumentException("A max sat solver is required for target-oriented solving.");			
		
		this.options = options;
		this.solver = solver();
	}

	/**
	 * {@inheritDoc}
	 */
	public ExtendedOptions options() {
		return options;
	}

	/**
	 * {@inheritDoc}
	 */
	public void free() {
		solver.free();
		if (!Options.isDebug()) {
			File dir = new File(options.uniqueName());
			if (dir.exists()) {
				File[] contents = dir.listFiles();
			    if (contents != null)
			        for (File f : contents)
			            f.delete();
			    dir.delete();
			}
		}
		
	}

	/**
	 * Calculates the solver that will be used, given the specified options.
	 * This may be a regular {@link Solver regular Kodkod solver}, a
	 * {@link DecomposedPardinusSolver decomposed Pardinus solver}, a
	 * {@link TemporalPardinusSolver temporal Pardinus solver} or an
	 * {@link ElectrodSolver Electrod solver}. The decomposed solver will use a
	 * regular Kodkod solver for the partial problem and a temporal Pardinus
	 * solver or an Electrod solver for the remainder.
	 * 
	 * @return the solver to be used internally.
	 */
	private AbstractSolver<PardinusBounds,ExtendedOptions> solver() {
		assert options.temporal() || !options.unbounded();
		assert !options.unbounded() || options.solver().unbounded();
		
		if (options.unbounded() && !options.solver().unbounded())
			throw new IllegalArgumentException("Cannot run complete with purely bounded solver.");

		if (!options.temporal() && options.solver().unbounded())
			throw new IllegalArgumentException("Cannot run static with complete model checkers.");

		if (options.decomposed()) {

			if (options.temporal()) {
				TemporalSolver<ExtendedOptions> solver2;
				if (options.solver().toString().equals("electrod"))
					solver2 = new ElectrodSolver(options);
				else 
					solver2 = new TemporalPardinusSolver(options);
				DecomposedPardinusSolver<TemporalSolver<ExtendedOptions>> solver = new DecomposedPardinusSolver<TemporalSolver<ExtendedOptions>>(options,solver2);
				return solver;
			} else {
				ExtendedSolver solver2 = new ExtendedSolver(options);
				DecomposedPardinusSolver<ExtendedSolver> solver = new DecomposedPardinusSolver<ExtendedSolver>(options,solver2);
				return solver;
			}
			
		} else {

			if (options.temporal()) {
				TemporalSolver<ExtendedOptions> solver;
				if (options.solver().toString().equals("electrod"))
					solver = new ElectrodSolver(options);
				else 
					solver = new TemporalPardinusSolver(options);
				return solver;
			} else {
				ExtendedSolver solver = new ExtendedSolver(options);
				return solver;				
			}
			
		}
		
	}
	
	/**
	 * {@inheritDoc}
	 */
	public Solution solve(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {

		assert (!TemporalTranslator.isTemporal(formula) && !bounds.hasVarRelations()) || options.temporal();
		assert !options.unbounded() || options.temporal();

		return solver.solve(formula, bounds);

	}

	/**
	 * {@inheritDoc}
	 */
	public Explorer<Solution> solveAll(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {

		assert (!TemporalTranslator.isTemporal(formula) && !bounds.hasVarRelations()) || options.temporal();
		assert !options.unbounded() || options.temporal();
		assert options.maxTraceLength() - options.minTraceLength() >= 0;
//		assert options.solver().incremental();
		
		if (solver instanceof IterableSolver<?,?>) {
			Iterator<Solution> it = ((IterableSolver<PardinusBounds, ExtendedOptions>) solver).solveAll(formula, bounds);
			if (it instanceof Explorer)
				return (Explorer<Solution>) it;
			else {
				return new Explorer<Solution>() {
					
					@Override
					public Solution next() {
						return it.next();
					}
					
					@Override
					public boolean hasNext() {
						return it.hasNext();
					}
	
					@Override
					public Solution nextP() {
						throw new UnsupportedOperationException("Branching not supported for this solver.");
					}
	
					@Override
					public Solution nextC() {
						throw new UnsupportedOperationException("Branching not supported for this solver.");
					}
	
					@Override
					public Solution nextS(int state, int delta, Set<Relation> force) {
						throw new UnsupportedOperationException("Branching not supported for this solver.");
					}
	
					@Override
					public boolean hasNextP() {
						return false;
					}
	
					@Override
					public boolean hasNextC() {
						return false;
					}
				};
			}
		}
		else {
			Solution sl = solver.solve(formula, bounds);

			return new Explorer<Solution>() {
				boolean first = true;
				@Override
				public Solution next() {
					if (first) {
						first = !first;
						return sl;
					}
					else
						throw new UnsupportedOperationException("Selected solver does not support solution iteration.");
				}
				
				@Override
				public boolean hasNext() {
					return false;
				}
	
				@Override
				public Solution nextP() {
					throw new UnsupportedOperationException("Selected solver does not support scenario exploration.");
				}
	
				@Override
				public Solution nextC() {
					throw new UnsupportedOperationException("Selected solver does not support scenario exploration.");
				}
	
				@Override
				public Solution nextS(int state, int delta, Set<Relation> force) {
					throw new UnsupportedOperationException("Selected solver does not support scenario exploration.");
				}
	
				@Override
				public boolean hasNextP() {
					return false;
				}
	
				@Override
				public boolean hasNextC() {
					return false;
				}
			};
		}
	}

}