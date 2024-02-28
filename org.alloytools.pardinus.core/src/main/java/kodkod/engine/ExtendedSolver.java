package kodkod.engine;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATProver;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.satlab.WTargetSATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;

/** 
 * A computational engine for solving relational satisfiability problems. 
 * Such a problem is described by a {@link kodkod.ast.Formula formula} in 
 * first order relational logic; finite {@link kodkod.instance.Bounds bounds} on 
 * the value of each {@link Relation relation} constrained by the formula; and 
 * a set of {@link kodkod.engine.config.Options options} specifying, among other global 
 * parameters, the length of bitvectors that describe the meaning of 
 * {@link IntExpression integer expressions} in the given formula.  The options are 
 * usually reused between invocations to the {@linkplain #solve(Formula, Bounds) solve}
 * methods, so they are specified as a part of the {@linkplain KodkodSolver solver} state. 
 *
 * <p>
 * A {@link AbstractKodkodSolver} takes as input a relational problem and produces a 
 * satisfying model or an {@link Instance instance} of it, if one exists.  It can also 
 * produce a {@link Proof proof} of unsatisfiability for problems with no models, 
 * if the {@link kodkod.engine.config.Options options} specify the use of a 
 * {@linkplain SATProver proof logging SAT solver}.
 * </p> 
 * 
 * @specfield options: Options 
 * @author Emina Torlak 
 * @modified Nuno Macedo // [HASLab] model finding hierarchy
 * @modified Nuno Macedo // [HASLab] decomposed model finding
 * @modified Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model finding
 * @modified Tim Nelson (Retargeter, DefaultRetargeter)
 */
public class ExtendedSolver extends AbstractKodkodSolver<PardinusBounds,ExtendedOptions> implements
		TargetOrientedSolver<ExtendedOptions>,
		SymbolicSolver<ExtendedOptions> {

	private ExtendedOptions options;

	/**
	 * Returns the Options object used by this Solver
	 * to guide translation of formulas from first-order
	 * logic to cnf.
	 * @return this.options
	 */
	public ExtendedOptions options() {
		return options;
	}
	
	/**
	 * Constructs a new Solver with the default options.
	 * @ensures this.options' = new Options()
	 */
	public ExtendedSolver() {
		this.options = new ExtendedOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * @ensures this.options' = options
	 * @throws NullPointerException  options = null
	 */
	public ExtendedSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();
		this.options = options;
	}
	
	/**
	 * An iterator over all solutions of a model.
	 * 
	 * A target-oriented iterator over all solutions of a model, adapted from {@link SolutionIterator}.
	 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model finding
	 * @author Emina Torlak
	 */
	// [HASLab]
	public final static class SolutionIterator implements Iterator<Solution> {
		private Translation.Whole translation;
		private long translTime;
		private int trivial;
		private ExtendedOptions opt; // [HASLab] TO mode
		private Map<String, Integer> weights; // [HASLab] signature weights
		
		/**
		 * Constructs a solution iterator for the given formula, bounds, and options.
		 */
		SolutionIterator(Formula formula, Bounds bounds, ExtendedOptions options) {
			if (options.targetoriented() && !options.solver().maxsat())
				throw new IllegalArgumentException("A max sat solver is required for target-oriented solving.");			

			this.opt = options;
			this.translTime = System.currentTimeMillis();
			this.translation = Translator.translate(formula, bounds, options);
			this.translTime = System.currentTimeMillis() - translTime;
			this.trivial = 0;
		}
		
		/**
		 * Returns true if there is another solution.
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {  return translation != null; }
		
		/**
		 * Returns the next solution if any.
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			if (!hasNext()) throw new NoSuchElementException();			
			// TODO: [HASLab] trivial solutions not yet supported in TO
			if (opt.targetoriented() && translation.trivial())
				throw new RuntimeException("Trivial problems with targets not yet supported.");

			try {
				return translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution();
			} catch (SATAbortedException sae) {
				translation.cnf().free();
				throw new AbortedException(sae);
			}
		}

		/** @throws UnsupportedOperationException */
		public void remove() { throw new UnsupportedOperationException(); }
		
		/**
		 * Solves {@code translation.cnf} and adds the negation of the
		 * found model to the set of clauses.  The latter has the 
		 * effect of forcing the solver to come up with the next solution
		 * or return UNSAT. If {@code this.translation.cnf.solve()} is false, 
		 * sets {@code this.translation} to null.
		 * @requires this.translation != null
		 * @ensures this.translation.cnf is modified to eliminate
		 * the  current solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextNonTrivialSolution() {
			final Translation.Whole transl = translation;
			final SATSolver cnf = transl.cnf();
			if (opt.targetoriented()) {
				Retargeter retargeter =
						(opt.retargeter() == null) ? new DefaultRetargeter() : opt.retargeter();
	
				// [HASLab] add the targets to generate the following solution
				// during solution iteration targets are added directly to the
				// SAT rather than through the bounds since the cnf is not
				// reconstructed at each step
				try {				
					cnf.valueOf(1); // fails if no previous solution
					assert(opt == transl.options()); // assume: opts unmodified
					retargeter.retarget(transl);

				} 
				catch(IllegalStateException e) { }
	
			}
			opt.reporter().solvingCNF(0, transl.numPrimaryVariables(), cnf.numberOfVariables(), cnf.numberOfClauses()); // [HASLab]
			
			final long startSolve = System.currentTimeMillis();
			final boolean isSat = cnf.solve();
			final long endSolve = System.currentTimeMillis();

			int primaryVars = transl.numPrimaryVariables();

			final Statistics stats = new Statistics(transl, translTime, endSolve - startSolve);
			final Solution sol;
			if (isSat) {			
				// extract the current solution; can't use the sat(..) method because it frees the sat solver
				sol = Solution.satisfiable(stats, transl.interpret());
				// add the negation of the current model to the solver
				final int[] notModel = new int[primaryVars];
				for(int i = 1; i <= primaryVars; i++) {
					notModel[i-1] = cnf.valueOf(i) ? -i : i;
				}
				cnf.addClause(notModel);
			} else {
				sol = unsat(transl, stats); // this also frees up solver resources, if any
				translation = null; // unsat, no more solutions
			}
			return sol;
		}
		
		/**
		 * Returns the trivial solution corresponding to the trivial translation stored in {@code this.translation},
		 * and if {@code this.translation.cnf.solve()} is true, sets {@code this.translation} to a new translation 
		 * that eliminates the current trivial solution from the set of possible solutions.  The latter has the effect 
		 * of forcing either the translator or the solver to come up with the next solution or return UNSAT.
		 * If {@code this.translation.cnf.solve()} is false, sets {@code this.translation} to null.
		 * @requires this.translation != null
		 * @ensures this.translation is modified to eliminate the current trivial solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextTrivialSolution() {
			if (opt.targetoriented())
				throw new UnsupportedOperationException("Trivial target-oriented next not yet supported.");

			final Translation.Whole transl = this.translation;
			
			final Solution sol = trivial(transl, translTime); // this also frees up solver resources, if unsat
			if (sol.instance()==null) {
				translation = null; // unsat, no more solutions
			} else {
				trivial++;
				
				final Bounds bounds = transl.bounds();
				// [HASLab] proper decomposed clone
				final Bounds newBounds = bounds instanceof PardinusBounds?((PardinusBounds) bounds).clone():bounds.clone();
				final List<Formula> changes = new ArrayList<Formula>();

				// [HASLab] when integrated consider the amalgamated problem to generate the formula,
				// otherwise already fixed relations will be ignored in symmetry breaking
				Bounds full_bounds = bounds;
				if (bounds instanceof PardinusBounds && ((PardinusBounds) bounds).integrated)
					full_bounds = ((PardinusBounds) bounds).amalgamated;
				
				for(Relation r : full_bounds.relations()) {
					final TupleSet lower = full_bounds.lowerBound(r); 
					if (lower != full_bounds.upperBound(r)) { 
						// r may change
						if (bounds.lowerBound(r).isEmpty()) { 
							changes.add(r.some());
						} else {
							final Relation rmodel = Relation.nary(r.name()+"_"+trivial, r.arity());
							newBounds.boundExactly(rmodel, bounds.lowerBound(r));	
							changes.add(r.eq(rmodel).not());
						}
					}
				}

				// nothing can change => there can be no more solutions (besides the current trivial one).
				// note that transl.formula simplifies to the constant true with respect to 
				// transl.bounds, and that newBounds is a superset of transl.bounds.
				// as a result, finding the next instance, if any, for transl.formula.and(Formula.or(changes)) 
				// with respect to newBounds is equivalent to finding the next instance of Formula.or(changes) alone.
				final Formula formula = changes.isEmpty() ? Formula.FALSE : Formula.or(changes);
				
				final long startTransl = System.currentTimeMillis();
				translation = Translator.translate(formula, newBounds, transl.options());
				translTime += System.currentTimeMillis() - startTransl;
			} 
			return sol;
		}
		
		/**
		 * Calculates the next TO solutions with weights.
		 * @param i the TO mode
		 * @param weights the signature weights
		 */
		// [HASLab]
		public Solution next(Map<String, Integer> weights) {
			if (opt.targetoriented()) {
				if (!(opt.solver().instance() instanceof TargetSATSolver))
					throw new AbortedException("Selected solver ("+opt.solver()+") does not have support for targets.");				
				if (weights != null) {
					if (!(opt.solver().instance() instanceof WTargetSATSolver))
						throw new AbortedException("Selected solver ("+opt.solver()+") does not have support for targets with weights.");				
				}
			}
			this.weights = weights;
			return next();
		}

		/**
		 * Implements the default behavior of retargeting to the last instance found.
		 * Uses the options' targetMode to decide whether to seek far from or close to the target.
		 */
		private class DefaultRetargeter implements Retargeter {

			@Override
			public void retarget(Translation transl) {
				assert(transl.cnf() instanceof TargetSATSolver);
				TargetSATSolver tcnf = (TargetSATSolver)transl.cnf();
				assert(transl.options() instanceof ExtendedOptions);
				ExtendedOptions opts = (ExtendedOptions) transl.options();
				tcnf.clearTargets();
				// [HASLab] if there are weights must iterate through the relations to find the literal's owner
				if (weights != null) {
					WTargetSATSolver wcnf = (WTargetSATSolver) tcnf;
					for (Relation r : transl.bounds().relations()) {
						Integer w = weights.get(r.name());
						if (r.name().equals("Int/next") || r.name().equals("seq/Int") || r.name().equals("String")) {}
						else {
							if (w==null) { w = 1; }
							IntIterator is = transl.primaryVariables(r).iterator();
							while (is.hasNext()) {
								int i = is.next();
								// [HASLab] add current model as weighted target
								if (opts.targetMode() == TMode.CLOSE) wcnf.addWeight(tcnf.valueOf(i) ? i : -i,w);
								if (opts.targetMode() == TMode.FAR) wcnf.addWeight(tcnf.valueOf(i) ? -i : i,w);
							}
						}
					}
				}
				// [HASLab] if there are no weights may simply iterate literals
				else {
					for(int i = 1; i <= transl.numPrimaryVariables(); i++) {
						// [HASLab] add current model as target
						if (opts.targetMode() == TMode.CLOSE) tcnf.addTarget(tcnf.valueOf(i) ? i : -i);
						if (opts.targetMode() == TMode.FAR) tcnf.addTarget(tcnf.valueOf(i) ? -i : i);
					}
				}
			}
		}
	}
	
	// [HASLab]
	@Override
	protected Iterator<Solution> iterator(Formula formula, Bounds bounds, Options options) {
		return new SolutionIterator(formula, bounds, options());
	}
		
}