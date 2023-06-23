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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.engine.fol2sat;

import static kodkod.engine.fol2sat.FormulaFlattener.flatten;
import static kodkod.engine.fol2sat.Skolemizer.skolemize;
import static kodkod.util.collections.Containers.setDifference;
import static kodkod.util.nodes.AnnotatedNode.annotate;
import static kodkod.util.nodes.AnnotatedNode.annotateRoots;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.ExtendedSolver;
import kodkod.engine.bool.BooleanAccumulator;
import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.BooleanValue;
import kodkod.engine.bool.Int;
import kodkod.engine.bool.Operator;
import kodkod.engine.config.Options;
import kodkod.engine.decomp.DecompFormulaSlicer;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.satlab.WTargetSATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

/** 
 * Translates, evaluates, and approximates {@link Node nodes} with
 * respect to given {@link Bounds bounds} (or {@link Instance instances}) and {@link Options}.
 * 
 * @author Emina Torlak 
 * @modified Nuno Macedo // [HASLab] decomposed model finding, symbolic model finding
 * @modified Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model finding
 */
public final class Translator {
	
	/*---------------------- public methods ----------------------*/
	/**
	 * Overapproximates the value of the given expression using the provided bounds and options.
	 * @return a BooleanMatrix whose TRUE entries represent the tuples contained in a sound overapproximation
	 * of the expression.
	 * @throws expression = null || instance = null || options = null
	 * @throws UnboundLeafException  the expression refers to an undeclared variable or a relation not mapped by the instance
	 * @throws HigherOrderDeclException  the expression contains a higher order declaration
	 */
	public static BooleanMatrix approximate(Expression expression, Bounds bounds, Options options) {
        Environment<BooleanMatrix, Expression> emptyEnv = Environment.empty(); // [AM]
        return FOL2BoolTranslator.approximate(annotate(expression), LeafInterpreter.overapproximating(bounds, options), emptyEnv);	}
	
	/**
	 * Evaluates the given formula to a BooleanConstant using the provided instance and options.
	 *
	 * @return a BooleanConstant that represents the value of the formula.
	 * @throws NullPointerException  formula = null || instance = null || options = null
	 * @throws UnboundLeafException  the formula refers to an undeclared variable or a relation not mapped by the instance
	 * @throws HigherOrderDeclException  the formula contains a higher order declaration
	 */
	public static BooleanConstant evaluate(Formula formula, Instance instance, Options options) {
		final LeafInterpreter interpreter = LeafInterpreter.exact(instance, options);
		final BooleanConstant eval = (BooleanConstant) FOL2BoolTranslator.translate(annotate(formula), interpreter);
		//TODO: check OF
//		final BooleanFactory factory = interpreter.factory();
//        BooleanConstant overflow = (BooleanConstant) factory.of();
//        if (options.noOverflow() && overflow.booleanValue()) { //[AM]
//            eval = BooleanConstant.FALSE;
//        }
        return eval;
	}
	
	/**
	 * Evaluates the given expression to a BooleanMatrix using the provided instance and options.
	 * 
	 * @return a BooleanMatrix whose TRUE entries represent the tuples contained by the expression.
	 * @throws NullPointerException  expression = null || instance = null || options = null
	 * @throws UnboundLeafException  the expression refers to an undeclared variable or a relation not mapped by the instance
	 * @throws HigherOrderDeclException  the expression contains a higher order declaration
	 */
	public static BooleanMatrix evaluate(Expression expression,Instance instance, Options options) {
		return (BooleanMatrix) FOL2BoolTranslator.translate(annotate(expression), LeafInterpreter.exact(instance, options));
	}

	/**
	 * Evalutes the given intexpression to an {@link kodkod.engine.bool.Int} using the provided instance and options.
	 * @return an {@link kodkod.engine.bool.Int} representing the value of the intExpr with respect
	 * to the specified instance and options.
	 * @throws NullPointerException  formula = null || instance = null || options = null
	 * @throws UnboundLeafException  the expression refers to an undeclared variable or a relation not mapped by the instance
	 * @throws HigherOrderDeclException  the expression contains a higher order declaration
	 */
	public static Int evaluate(IntExpression intExpr, Instance instance, Options options) {
		LeafInterpreter interpreter = LeafInterpreter.exact(instance, options);
        Int ret = (Int) FOL2BoolTranslator.translate(annotate(intExpr), interpreter);
        //TODO: check OF
//		BooleanFactory factory = interpreter.factory();
//		BooleanConstant bc = (BooleanConstant) factory.of();
//		boolean overflow = false;
//		if (options.noOverflow() && bc.booleanValue()) //[AM]
//		    overflow = true;
//		ret.setOverflowFlag(overflow);
		return ret;
	}
	
	/**
	 * Translates the given formula using the specified bounds and options.
	 * The CNF representation of the given formula and bounds  is generated so that the magnitude 
	 * of the literal representing the truth value of a given circuit is strictly larger than the magnitudes of 
	 * the literals representing the truth values of the circuit's descendants.   
	 * @return some t: Translation.Whole |  t.originalFormula = formula && t.originalBounds = bounds && t.options = options
	 * @throws NullPointerException  any of the arguments are null
	 * @throws UnboundLeafException  the formula refers to an undeclared variable or a relation not mapped by the given bounds.
	 * @throws HigherOrderDeclException  the formula contains a higher order declaration that cannot
	 * be skolemized, or it can be skolemized but options.skolemize is false.
	 */
	public static Translation.Whole translate(Formula formula, Bounds bounds, Options options)  {
		return (Translation.Whole) (new Translator(formula,bounds,options)).translate();
	}

	/**
	 * Translates the given formula using the specified bounds and options in such a way 
	 * that the resulting translation can be extended with additional formulas and bounds, subject to 
	 * the same options.  We require that the options specify  an incremental SAT solver, and no translation logging.
	 * The CNF representation of the given formula and bounds  is generated so that the magnitude 
	 * of the literal representing the truth value of a given circuit is strictly larger than the magnitudes of 
	 * the literals representing the truth values of the circuit's descendants.  
	 * @requires options.solver.incremental() && options.logTranslation = 0  
	 * @return some t: Translation.Incremental |  t.originalFormula = formula && t.originalBounds = bounds && t.options = options
	 * @throws NullPointerException  any of the arguments are null
	 * @throws UnboundLeafException  the formula refers to an undeclared variable or a relation not mapped by the given bounds
	 * @throws HigherOrderDeclException  the formula contains a higher order declaration
	 * @throws IllegalArgumentException any of the preconditions on options are violated
	 */
	public static Translation.Incremental translateIncremental(Formula formula, Bounds bounds, Options options)  {
		checkIncrementalOptions(options);	
		return (Translation.Incremental) (new Translator(formula, bounds, options, true)).translate();
	}
	
	/**
	 * Updates the given translation with {@code CNF(formula, translation.originalBounds + bounds, translation.options)}.  The 
	 * result of the update is either a new translation instance or the given {@code translation}, modified in place.  We assume
	 * that client did not modify any translation state between invocations to {@code translateIncremental(...)}.
	 * 
	 * <p>
	 * We require {@code bounds} and {@code translation} to be consistent in the following sense:
	 * <ol>
	 * <li>{@code bounds} and {@code translation.bounds} share the same universe;</li>
	 * <li>{@code bounds} must not specify any integer bounds;</li> 
	 * <li>{@code bounds.relations} must not contain any members of {@code translation.bounds.relations} 
	 * (which may be a superset of {@code translation.originalBounds.relations} that also includes Skolem constants); and,</li>
	 * <li>{@code bounds} must induce a coarser set of equivalence classes on the shared universe than {@code translation.originalBounds}.</li>
	 * </ol>
	 * </p>
	 * 
	 * <p>
	 * The behavior of this method is unspecified if a prior call to {@code translation.cnf.solve()} returned false, or 
	 * if a prior call to this method resulted in an exception.
	 * </p>
	 * 
	 * @requires translation.cnf.solve()
	 * @requires formula.*components & Relation in (translation.bounds + bounds).relations
	 * @requires translation.bounds.universe = bounds.universe && no bounds.intBound && no (translation.bounds.relations & bounds.relations)
	 * @requires all s: translation.symmetries | 
	 *            some p: {@link SymmetryDetector#partition(Bounds) partition}(bounds) |
	 *             s.ints in p.ints       
	 * @return some t: Translation | 
	 *          t.originalFormula = translation.originalFormula.and(formula) && 
	 * 	        t.originalBounds.relations = translation.originalBounds.relations + bounds.relations &&
	 *          t.originalBounds.upperBound = translation.originalBounds.upperBound + bounds.upperBound &&
	 *          t.originalBounds.lowerBound = translation.originalBounds.lowerBound + bounds.lowerBound &&
	 *          t.originalBounds.intBound = translation.originalBounds.intBound 
	 * @throws NullPointerException  any of the arguments are null
	 * @throws UnboundLeafException  the formula refers to an undeclared variable or a relation not mapped by translation.bounds + bounds
	 * @throws HigherOrderDeclException  the formula contains a higher order declaration
	 * @throws IllegalArgumentException any of the other preconditions on the arguments are violated
	 */
	public static Translation.Incremental translateIncremental(Formula formula, Bounds bounds, Translation.Incremental translation)  {
		checkIncrementalOptions(translation.options());
		checkIncrementalBounds(bounds, translation);		
		if (translation.trivial())  { 
			return translateIncrementalTrivial(formula, bounds, translation);
		} else {
			return translateIncrementalNonTrivial(formula, bounds, translation);
		}	
	}

	/** 
	 * @requires checkIncrementalBounds(bounds, transl)
	 * @requires checkIncrementalOptions(transl.options) 
	 * @requires transl.trivial()
	 * @requires transl.cnf.solve()
	 * @return see {@link #translateIncremental(Formula, Bounds, Options)}
	 **/
	private static Translation.Incremental translateIncrementalTrivial(Formula formula, Bounds bounds, Translation.Incremental transl) {
		if (!transl.cnf().solve()) 
			throw new IllegalArgumentException("Expected a satisfiable translation, given " + transl);
		
		transl.cnf().free(); // release the old empty solver since we are going to re-translate
		
		final Options tOptions = transl.options();
		final Bounds tBounds = transl.bounds();
		
		// add new relation bindings to the translation bounds.  since the given bounds induce
		// a coarser set of symmetries on the universe than transl.symmetries, adding their (disjoint) bindings to tBounds 
		// will not change the symmetries of tBounds.  note that the ymmetries of tBounds refine transl.symmetries, and they 
		// may be strictly finer if some of the symmetries in transl.symmetries were broken via SymmetryBreaker.breakMatrixSymmetries(...) 
		// during the generation of transl.  in particular, any symmetries absent from tBounds are precisely those that were broken based
		// on the total ordering and acyclic predicates in transl.originalFormula.
		for(Relation r : bounds.relations()) {
			tBounds.bound(r, bounds.lowerBound(r), bounds.upperBound(r));
		}
		
		// re-translate the given formula with respect to tBounds.  note that we don't have to re-translate 
		// the conjunction of transl.formula and formula since transl.formula is guaranteed to evaluate to 
		// TRUE with respect to tBounds (since no bindings that were originally in tBounds were changed by the above loop).
		final Translation.Incremental updated = translateIncremental(formula, tBounds, tOptions);
		
		// we can't return the updated translation as is, since we have to make sure that updated.symmetries is set to
		// transl.symmetries rather than the potentially finer set of symmetries induced by tBounds. note that 
		// the updated translation currently has updated.originalBounds = tBounds, while updated.bounds is a copy of 
		// tBounds with possibly additional skolem relations, as well as new bounds for some relations in formula.*components 
		// due to symmetry breaking.
		return new Translation.Incremental(updated.bounds(), tOptions, transl.symmetries(), updated.interpreter(), updated.incrementer());
	}
	
	/** 
	 * @requires checkIncrementalBounds(bounds, transl)
	 * @requires checkIncrementalOptions(transl.options) 
	 * @requires !transl.trivial()
	 * @return see {@link #translateIncremental(Formula, Bounds, Options)}
	 **/
	private static Translation.Incremental translateIncrementalNonTrivial(Formula formula, Bounds bounds, Translation.Incremental transl) {
		
		final Options tOptions = transl.options();
		final Bounds tBounds = transl.bounds();
		
		// save the set of relations bound in the pre-state
		final Set<Relation> oldRelations = new LinkedHashSet<Relation>(tBounds.relations());
		
		// add new relation bindings to the translation bounds.  note that skolemization (below) may also cause extra relations to be added.
		for(Relation r : bounds.relations()) {
			tBounds.bound(r, bounds.lowerBound(r), bounds.upperBound(r));
		}
		final AnnotatedNode<Formula> annotated = 
			(transl.options().skolemDepth() < 0) ? annotate(formula) : skolemize(annotate(formula), tBounds, tOptions);
		
		// extend the interpreter with variable allocations for new relations, either from given bounds
		// or those introduced by skolemization
		final LeafInterpreter interpreter = transl.interpreter();
		interpreter.extend(setDifference(tBounds.relations(), oldRelations), tBounds.lowerBounds(), tBounds.upperBounds());
		
		final BooleanValue circuit = FOL2BoolTranslator.translate(annotated, interpreter); 
	
		if (circuit==BooleanConstant.FALSE) {
			// release the old solver and state, and return a fresh trivially false incremental translation.
			transl.incrementer().solver().free();
			return new Translation.Incremental(tBounds, tOptions, transl.symmetries(), 
					LeafInterpreter.empty(tBounds.universe(), tOptions), 
					Bool2CNFTranslator.translateIncremental(BooleanConstant.FALSE, tOptions.solver()));			
		} else if (circuit==BooleanConstant.TRUE) {
			// must add any newly allocated primary variables to the solver for interpretation to work correctly 
			final int maxVar = interpreter.factory().maxVariable();
			final int cnfVar = transl.cnf().numberOfVariables();
			if (maxVar > cnfVar) {
				transl.cnf().addVariables(maxVar-cnfVar);
			}
		} else {
			// circuit is a formula; add its CNF representation to transl.incrementer.solver()			
			Bool2CNFTranslator.translateIncremental((BooleanFormula) circuit, interpreter.factory().maxVariable(), transl.incrementer());			
		}  
		
		return transl;
	}
	
	/**
	 * Checks that the given options are suitable for incremental translation.
	 * @requires options.solver.incremental() && options.logTranslation = 0  
	 * @throws IllegalArgumentException any of the preconditions are violated
	 */
	public static void checkIncrementalOptions(Options options) {
		if (!options.solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required for incremental translation: " + options);
		if (options.logTranslation() != 0)
			throw new IllegalArgumentException("Translation logging must be disabled for incremental translation: " + options);
	}
	
	/**
	 * Checks that the given {@code inc} bounds are incremental with respect to the given {@code translation}.
	 * @requires translation.bounds.universe = inc.universe && no inc.intBound && no (translation.bounds.relations & inc.relations)
	 * @requires all s: translation.symmetries |  
	 * 				some p: {@link SymmetryDetector#partition(Bounds) partition}(inc) | 
	 * 				   s.elements in p.elements
	 * @throws IllegalArgumentException any of the preconditions are violated
	 */
	public static void checkIncrementalBounds(Bounds inc, Translation.Incremental translation) {
		final Bounds base = translation.bounds();
		if (!base.universe().equals(inc.universe()))
			incBoundErr(inc.universe(), "universe", "equal to", base.universe());
		if (!inc.intBounds().isEmpty()) 
			incBoundErr(inc.intBounds(), "intBound", "empty, with integer bounds fully specified by", base.intBounds());
		if (inc.relations().isEmpty()) return;
		final Set<Relation> baseRels = base.relations();
		for(Relation r : inc.relations()) { 
			if (baseRels.contains(r)) {
				incBoundErr(inc.relations(), "relations", "disjoint from", baseRels);
			}  
 		}
		final Set<IntSet> symmetries = translation.symmetries();
		final Set<IntSet> incSymmetries = SymmetryDetector.partition(inc);
		EQUIV_CHECK : for(IntSet part : symmetries) {
			for(IntSet incPart : incSymmetries) {
				if (incPart.containsAll(part))
					continue EQUIV_CHECK;
			}
			incBoundErr(incSymmetries, "partition", "coarser than", symmetries);
		}
	}
	
	/**
	 * Throws an {@link IllegalArgumentException} with an error message that describes why given bounds 
	 * cannot be used for incremental translation.  
	 */
	private static void incBoundErr(Object newObj, String desc, String relatedTo, Object translObj) {
		final String newDesc = "bounds." + desc, oldDesc = "translation.originalBounds." + desc;
		throw new IllegalArgumentException("Expected " + newDesc + " to be " + relatedTo + " " + oldDesc + 
				" for incremental translation; given "+ newDesc + " = " + newObj + ", " + oldDesc + " = " + translObj);
	}
	
	
	/*---------------------- private translation state and methods ----------------------*/
	/**
	 * @specfield originalFormula: Formula
	 * @specfield originalBounds: Bounds
	 * @specfield bounds: Bounds
	 * @specfield options: Options
	 * @specfield incremental: boolean
	 */
	private final Formula originalFormula;
	private final Bounds originalBounds;
	private final Bounds bounds;
	private final Options options;
	private final boolean logging;
	private final boolean incremental;
	
	/**
	 * Constructs a Translator for the given formula, bounds, options and incremental flag.
	 * If the flag is true, then the translator produces an initial {@linkplain Translation.Incremental incremental translation}.
	 * Otherwise, the translator produces a {@linkplain Translation.Whole basic translation}.
	 * @ensures this.originalFormula' = formula and 
	 * 	this.options' = options and 
	 *  this.originalBounds' = bounds and 
	 * 	this.bounds' = bounds.clone() and
	 *  this.incremental' = incremental 
	 */
	private Translator(Formula formula, Bounds bounds, Options options, boolean incremental) {
		// [HASLab] retrieve the additional formula imposed by the symbolic
		// bounds, depending on execution stage
		Formula symbForm = Formula.TRUE;
		
		this.bounds = bounds.clone();
		if (this.bounds instanceof PardinusBounds) {
			// [HASLab] if decomposed mode, the amalgamated bounds are always considered
			if (options.decomposed() && ((PardinusBounds) this.bounds).amalgamated() != null)
				symbForm = ((PardinusBounds) this.bounds).amalgamated().resolve(options.reporter());
			// [HASLab] then regular bounds
			symbForm = symbForm.and(((PardinusBounds) this.bounds).resolve(options.reporter()));
		}
					
		this.originalFormula = formula.and(symbForm);
		this.originalBounds = this.bounds.clone();
		this.options = options;
		this.logging = options.logTranslation()>0;
		this.incremental = incremental;
	}
	
	/**
	 * Constructs a non-incremental Translator for the given formula, bounds and options.
	 * @ensures this(formula, bounds, options, false)
	 */
	private Translator(Formula formula, Bounds bounds, Options options) {
		this(formula, bounds, options, false);
	}
	
	/**
	 * Translates this.originalFormula with respect to this.bounds and this.options. If this.incremental is true, 
	 * then the returned translation is {@linkplain Translation.Incremental incremental}; otherwise the output is
	 * a {@linkplain Translation.Whole basic} translation.
	 * @return a {@linkplain Translation} whose solver is a SATSolver instance initialized with the 
	 * CNF representation of the given formula, with respect to the given bounds.  The CNF
	 * is generated in such a way that the magnitude of a literal representing the truth
	 * value of a given formula is strictly larger than the magnitudes of the literals representing
	 * the truth values of the formula's descendants.  
	 * @throws UnboundLeafException  this.originalFormula refers to an undeclared variable or a relation not mapped by this.bounds.
	 * @throws HigherOrderDeclException  this.originalFormula contains a higher order declaration that cannot
	 * be skolemized, or it can be skolemized but this.options.skolemDepth < 0
	 */
	private Translation translate() {

		final AnnotatedNode<Formula> originalAnnotated = logging ? annotateRoots(originalFormula) : annotate(originalFormula);
		// Remove bindings for unused relations/ints if this is not an incremental translation.  If it is
		// an incremental translation, we have to keep all bindings since they may be used later on.
	
		AnnotatedNode<Formula> actualAnnotated = originalAnnotated;
		if (!incremental) {
			// [HASLab] if dealing with a decomposed problem, split and remove spurious variables from amalgamated as well
			if (bounds instanceof PardinusBounds) {
				PardinusBounds pbounds = (PardinusBounds) bounds;
				if (options.decomposed() && pbounds.amalgamated() != null) { // to avoid entering for hybrid
					Entry<Formula, Formula> slices = DecompFormulaSlicer.slice(originalFormula, pbounds);
					Formula actual = pbounds.integrated()?slices.getValue():slices.getKey();
					options.reporter().debug("sliced formula: "+actual);
					actualAnnotated = logging ? annotateRoots(actual) : annotate(actual);
					pbounds.amalgamated().relations().retainAll(originalAnnotated.relations());
					if (!originalAnnotated.usesInts()) pbounds.amalgamated().ints().clear();
				} 
			}
			// [HASLab] retain the relations for the sliced formula
			bounds.relations().retainAll(actualAnnotated.relations());
			if (!actualAnnotated.usesInts()) bounds.ints().clear();
		}

		// Detect symmetries.
		final SymmetryBreaker breaker = new SymmetryBreaker(bounds, options.reporter());
		// Optimize formula and bounds by using symmetry information to tighten bounds and 
		// eliminate top-level predicates, and also by skolemizing.  Then translate the optimize
		// formula and bounds to a circuit, augment the circuit with a symmetry breaking predicate 
		// that eliminates any remaining symmetries, and translate everything to CNF.
		return toBoolean(optimizeFormulaAndBounds(actualAnnotated, breaker), breaker);
	}
	
	/**
	 * <p>When logging is disabled, optimizes annotated.node by first breaking matrix symmetries on its top-level predicates,
	 * replacing them with the simpler formulas generated by 
	 * {@linkplain SymmetryBreaker#breakMatrixSymmetries(Map, boolean) breaker.breakMatrixSymmetries(...)}, 
	 * and skolemizing the result, if applicable.</p>
	 * 
	 * <p> When logging is enabled, optimizes annotated.node by first flattening it into a set of conjuncts, 
	 * assuming that core granularity is 1.  This involves pushing negations through quantifier-free formulas.
	 * We then skolemize, followed by an additional layer of flattening (if this.options.coreGranularity > 1), 
	 * possibly through quantifiers (if this.options.coreGranuarity is 3).  Predicate inlining and breaking of
	 * matrix symmetries is performed last to  prevent any quantified formulas generated by predicate inlining 
	 * from also being flattened (as this wouldn't be meaningful at the level of the original formula).</p> 
	 * 
	 * @requires SAT(annotated.node, this.bounds, this.options) iff SAT(this.originalFormula, this.originalBounds, this.options)
	 * @requires annotated.node.*components & Relation = this.originalFormula.*components & Relation
	 * @requires breaker.bounds = this.bounds
	 * @ensures this.bounds.relations in this.bounds.relations' 
	 * @ensures this.options.reporter().optimizingBoundsAndFormula()
	 * @return some f: AnnotatedNode<Formula> | meaning(f.node, this.bounds, this.options) = meaning(this.originalFormula, this.originalBounds, this.options)
	 */
	private AnnotatedNode<Formula> optimizeFormulaAndBounds(AnnotatedNode<Formula> annotated, SymmetryBreaker breaker) {	
		options.reporter().optimizingBoundsAndFormula();

		if (logging) {  
			final int coreGranularity = options.coreGranularity();
			if (coreGranularity==1) { 
				annotated = flatten(annotated, false);
			}
			if (options.skolemDepth()>=0) {
				annotated = skolemize(annotated, bounds, options);
			}
			if (coreGranularity>1) { 
				annotated = flatten(annotated, options.coreGranularity()==3);
			}
			return inlinePredicates(annotated, breaker.breakMatrixSymmetries(annotated.predicates(), false));
		} else {  			
			annotated = inlinePredicates(annotated, breaker.breakMatrixSymmetries(annotated.predicates(), true).keySet());
			return options.skolemDepth()>=0 ? Skolemizer.skolemize(annotated, bounds, options) : annotated;
		}
		
	}

	/**
	 * Returns an annotated formula f such that f.node is equivalent to annotated.node
	 * with its <tt>truePreds</tt> replaced with the constant formula TRUE and the remaining
	 * predicates replaced with equivalent constraints.
	 * @requires truePreds in annotated.predicates()[RelationnPredicate.NAME]
	 * @requires truePreds are trivially true with respect to this.bounds
	 * @return an annotated formula f such that f.node is equivalent to annotated.node
	 * with its <tt>truePreds</tt> replaced with the constant formula TRUE and the remaining
	 * predicates replaced with equivalent constraints.
	 */
	private AnnotatedNode<Formula> inlinePredicates(final AnnotatedNode<Formula> annotated, final Set<RelationPredicate> truePreds) {
		final AbstractReplacer inliner = new AbstractReplacer(annotated.sharedNodes()) {
			public Formula visit(RelationPredicate pred) {
				Formula ret = lookup(pred);
				if (ret!=null) return ret;
				return truePreds.contains(pred) ? cache(pred, Formula.TRUE) : cache(pred, pred.toConstraints());
			}
		};
		return annotate(annotated.node().accept(inliner));	
	}
	
	/**
	 * Returns an annotated formula f such that f.node is equivalent to annotated.node
	 * with its <tt>simplified</tt> predicates replaced with their corresponding Formulas and the remaining
	 * predicates replaced with equivalent constraints.  The annotated formula f will contain transitive source 
	 * information for each of the subformulas of f.node.  Specifically, let t be a subformula of f.node, and
	 * s be a descdendent of annotated.node from which t was derived.  Then, f.source[t] = annotated.source[s]. </p>
	 * @requires simplified.keySet() in annotated.predicates()[RelationPredicate.NAME]
	 * @requires no disj p, p': simplified.keySet() | simplified.get(p) = simplifed.get(p') // this must hold in order
	 * to maintain the invariant that each subformula of the returned formula has exactly one source
	 * @requires for each p in simplified.keySet(), the formulas "p and [[this.bounds]]" and
	 * "simplified.get(p) and [[this.bounds]]" are equisatisfiable
	 * @return an annotated formula f such that f.node is equivalent to annotated.node
	 * with its <tt>simplified</tt> predicates replaced with their corresponding Formulas and the remaining
	 * predicates replaced with equivalent constraints.
	 */
	private AnnotatedNode<Formula> inlinePredicates(final AnnotatedNode<Formula> annotated, final Map<RelationPredicate,Formula> simplified) {
		final Map<Node,Node> sources = new IdentityHashMap<Node,Node>();
		final AbstractReplacer inliner = new AbstractReplacer(annotated.sharedNodes()) {
			private RelationPredicate source =  null;			
			protected <N extends Node> N cache(N node, N replacement) {
				if (replacement instanceof Formula) {
					if (source==null) {
						final Node nsource = annotated.sourceOf(node);
						if (replacement!=nsource) 
							sources.put(replacement, nsource);
					} else {
						sources.put(replacement, source);
					}
				}
				return super.cache(node, replacement);
			}
			public Formula visit(RelationPredicate pred) {
				Formula ret = lookup(pred);
				if (ret!=null) return ret;
				source = pred;
				if (simplified.containsKey(pred)) {
					ret = simplified.get(pred).accept(this);
				} else {
					ret = pred.toConstraints().accept(this);
				}
				source = null;
				return cache(pred, ret);
			}
		};

		return annotate(annotated.node().accept(inliner), sources);
	}
	
	/**
	 * Translates the given annotated formula to a circuit, conjoins the circuit with an 
	 * SBP generated by the given symmetry breaker, and returns its {@linkplain Translation} to CNF.
	 * The SBP breaks any symmetries that could not be broken during the 
	 * {@linkplain #optimizeFormulaAndBounds(AnnotatedNode, SymmetryBreaker) formula and bounds optimization} step.
	 * @requires SAT(annotated.node, this.bounds, this.options) iff SAT(this.originalFormula, this.originalBounds, this.options)
	 * @requires breaker.bounds = this.bounds
	 * @ensures this.options.logTranslation => some this.log'
	 * @ensures this.options.reporter().translatingToBoolean(annotated.node(), this.bounds)
	 * @ensures this.options.reporter().generatingSBP()
	 * @return the translation of annotated.node with respect to this.bounds
	 */
	private Translation toBoolean(AnnotatedNode<Formula> annotated, SymmetryBreaker breaker) {
		
		// [HASLab] if temporal, throw a warning that will be reduced
		if (TemporalTranslator.isTemporal(annotated.node()))
			options.reporter().warning("Temporal formula: will be reduced to possibly unsound static version.");

		options.reporter().translatingToBoolean(annotated.node(), bounds);
		
		final LeafInterpreter interpreter = LeafInterpreter.exact(bounds, options, incremental);
		final BooleanFactory factory = interpreter.factory();
		
		if (logging) {
			assert !incremental;
			final TranslationLogger logger = options.logTranslation()==1 ? new MemoryLogger(annotated, bounds) : new FileLogger(annotated, bounds);
			final BooleanAccumulator circuit = FOL2BoolTranslator.translate(annotated, interpreter, logger);
			final TranslationLog log = logger.log();
			if (circuit.isShortCircuited()) { 
				return trivial(circuit.op().shortCircuit(), log, annotated.relations());
			} else if (circuit.size()==0) { 
				return trivial(circuit.op().identity(), log, annotated.relations());
			}
			circuit.add(breaker.generateSBP(interpreter, options));
			return toCNF((BooleanFormula)factory.accumulate(circuit), interpreter, log);
		} else {
			final BooleanValue circuit = (BooleanValue)FOL2BoolTranslator.translate(annotated, interpreter);
			BooleanValue sbp = breaker.generateSBP(interpreter, options); // [HASLab] for Electrod we need symmetries even when trivial
			if (circuit.op()==Operator.CONST) { 
				options.reporter().debug("trivial boolean circuit: "+circuit);
				return trivial((BooleanConstant)circuit, null, bounds.relations());
			} 
			return toCNF((BooleanFormula)factory.and(circuit, sbp), interpreter, null);
		}
	}
	
	/**
	 * Translates the given circuit to CNF, adds the clauses to a SATSolver returned
	 * by options.solver(), and returns a Translation object constructed from the solver
	 * and the provided arguments.
	 * @requires SAT(circuit) iff SAT(this.originalFormula, this.originalBounds, this.options)
	 * @requires circuit.factory = interpreter.factory
	 * @requires interpreter.universe = this.bounds.universe && interpreter.relations = this.bounds.relations() && 
	 *           interpreter.ints = this.bounds.ints() && interpreter.lbounds = this.bounds.lowerBound && 
	 *           this.interpreter.ubounds = bounds.upperBound && interpreter.ibounds = bounds.intBound 
	 * @requires log.originalFormula = this.originalFormula && log.bounds = this.bounds
	 * @ensures {@link #completeBounds()}
	 * @ensures this.options.reporter.translatingToCNF(circuit)
	 * @return some t: Translation | 
	 *           t.bounds = completeBounds() && t.originalBounds = this.originalBounds &&
	 *           t.vars = interpreter.vars &&
	 *           t.vars[Relation].int in t.solver.variables && 
	 *           t.solver.solve() iff SAT(this.formula, this.bounds, this.options)
	 */
	private Translation toCNF(BooleanFormula circuit, LeafInterpreter interpreter, TranslationLog log) {
		options.reporter().translatingToCNF(circuit);
		final int maxPrimaryVar = interpreter.factory().maxVariable();

		if (incremental) {
			final Bool2CNFTranslator incrementer = Bool2CNFTranslator.translateIncremental(circuit, maxPrimaryVar, options.solver());
			return new Translation.Incremental(completeBounds(), options, SymmetryDetector.partition(originalBounds), interpreter, incrementer);
		} else {
			final Map<Relation, IntSet> varUsage = interpreter.vars();
			final SATSolver cnf = Bool2CNFTranslator.translate((BooleanFormula)circuit, maxPrimaryVar, options.solver());
			// [HASLab] add the targets to the SAT problem
			if (bounds instanceof PardinusBounds) 
				doTargets((PardinusBounds) bounds, interpreter, cnf);

			interpreter = null; // enable gc

			return new Translation.Whole(completeBounds(), options, cnf, varUsage, maxPrimaryVar, log);
		}
	}

	/**
	 * Add the targets defined in the bounds to the SAT problem. Note that this
	 * process will only be performed once, as the iteration does not involve
	 * the bounds (see {@link ExtendedSolver#solveAll(Formula, Bounds)}).
	 * 
	 * @param bounds
	 *            the bounds where the targets are defined.
	 * @param interpreter
	 *            assigns boolean variables to the relations.
	 * @param cnf
	 *            the cnf to which to add the targets.
	 */
	// [HASLab]
	private void doTargets(PardinusBounds bounds, LeafInterpreter interpreter, final SATSolver cnf) {
		for (Relation r : bounds.targets().keySet()) {
			Integer w = bounds.weight(r);
			if (w == null)
				for (IndexedEntry<BooleanValue> e : interpreter.interpret(r)) {
					int x = e.value().label();
					if (e.value() instanceof BooleanConstant) ; // not a boolean variable;
					else if (bounds.target(r).indexView().contains(e.index()))
						((TargetSATSolver) cnf).addTarget(x);
					else
						((TargetSATSolver) cnf).addTarget(-x);
				}	
			else
				for (IndexedEntry<BooleanValue> e : interpreter.interpret(r)) {
					int x = e.value().label();
					if (e.value() instanceof BooleanConstant) ; // not a boolean variable;
					else if (bounds.target(r).indexView().contains(e.index()))
						((WTargetSATSolver) cnf).addWeight(x,w);
					else 
						((WTargetSATSolver) cnf).addWeight(-x,w);
				}				
		}
	}
	
	/**
	 * Returns a whole or incremental translation, depending on the value of {@code this.incremental}, 
	 * using the given trivial outcome, {@linkplain #completeBounds() completeBounds()}, {@code this.options}, 
	 * and the given log.
	 * @param set 
	 * @ensures {@link #completeBounds()}
	 * @return some t: Translation | 
	 *           t.bounds = completeBounds() && t.originalBounds = this.originalBounds &&
	 *           no t.solver.variables && 
	 *           no t.vars &&
	 *           (outcome.booleanValue() => no t.solver.clauses else (one t.solver.clauses && no t.solver.clauses.literals))      
	 **/
	@SuppressWarnings("unchecked")
	private Translation trivial(BooleanConstant outcome, TranslationLog log, Set<Relation> set) {
		if (incremental) {
			return new Translation.Incremental(completeBounds(), options, 
					SymmetryDetector.partition(originalBounds), 
					LeafInterpreter.empty(bounds.universe(), options), // empty interpreter
					Bool2CNFTranslator.translateIncremental(outcome, options.solver()));
		} else {
			return new Translation.Whole(completeBounds(), options, 
						Bool2CNFTranslator.translate(outcome, options.solver()), 
						Collections.EMPTY_MAP, 0, log);
		}
	}
	
	/**
	 * Completes {@code this.bounds} using the bindings from {@code this.originalBounds} so that 
	 * the result satisfies the {@linkplain Translation} invariants. This involves updating 
	 * {@code this.bounds} with bindings from {@code this.originalBounds}, if any, that had been discarded 
	 * in the {@link #translate() first step} of the translation.  The first step of a non-incremental 
	 * translation is to discard bounds for relations that are not constrained by {@code this.originalFormula}, 
	 * and to discard all integer bounds if {@code this.originalFormula} contains no integer expressions.  
	 * This is sound since any instance of {@code this.originalFormula} with respect to {@code this.originalBounds} only needs to 
	 * satisfy the lower bound constraint on each discarded relation/integer.   By updating {@code this.bounds} with 
	 * the bindings for discarded relations/integers for which no variables were allocated, we ensure that any instance returned by 
	 * {@linkplain Translation#interpret()} will bind those relations/integers to their lower bound, therefore satisfying 
	 * the original problem {@code (this.originalFormula, this.originalBounds, this.options)}.
	 * 
	 * @requires no this.bounds.intBound or this.bounds.intBound = this.originalBounds.intBound
	 * @ensures  this.bounds.relations' = this.bounds.relations + this.originalBounds.relations &&
	 *           this.bounds.intBound' = this.originalBounds.intBound &&
	 *           this.bounds.lowerBound' = this.bounds.lowerBound + (this.originalBounds.relations - this.bounds.relations)<:(this.originalBounds.lowerBound) &&
	 *           this.bounds.upperBound' = bounds.upperBound + (this.originalBounds.relations - this.bounds.relations)<:(this.originalBounds.upperBound)
	 * @return this.bounds
	 */
	private Bounds completeBounds() {
		final Bounds optimized = this.bounds; 
		final Bounds original = this.originalBounds;
		if (optimized.ints().isEmpty()) {
			for(IndexedEntry<TupleSet> entry : original.intBounds()) { 
				optimized.boundExactly(entry.index(), entry.value());
			}
		} else {
			assert optimized.intBounds().equals(original.intBounds());
		}
		final Set<Relation> rels = optimized.relations();
		for(Relation r : original.relations()) {
			if (!rels.contains(r)) {
				optimized.bound(r, original.lowerBound(r), original.upperBound(r));
			}
		}
		
		// [HASLab] consider the remainder bounds in decomposed problems.
		if (optimized instanceof PardinusBounds && ((PardinusBounds) original).integrated()) {
			PardinusBounds b = ((PardinusBounds) original).amalgamated();
			for(Relation r : b.relations()) {
				if (!((PardinusBounds) optimized).amalgamated().relations().contains(r)) {
					((PardinusBounds) optimized).amalgamated().bound(r, b.lowerBound(r), b.upperBound(r));
				}
			}
		}
		
		return optimized;
	}
}
