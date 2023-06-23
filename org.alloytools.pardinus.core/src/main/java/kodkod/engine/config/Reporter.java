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

import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.util.ints.IntSet;

/**
 * Enables passing of messages between the kodkod engine
 * and the client about the following stages of the analysis:
 * <ol>
 * <li>symmetry detection
 * <li>bounds and formula optimization (breaking of predicate symmetries, predicate inlining and skolemization)</li>
 * <li>translation to a boolean circuit</li>
 * <li>symmetry breaking predicate (SBP) generation</li>
 * <li>translation to cnf</li>
 * <li>running a sat solver on the generated cnf</li>
 * </ol>
 * Some of these stages may not be executed, depending on the 
 * {@link Options options} used for analysis.  
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] additional reporting
 */
public interface Reporter {

	/**
	 * Reports that symmetry detection started on the given bounds.
	 * The given bounds must not be mutated.
	 */
	public void detectingSymmetries(Bounds bounds);
	
	/**
	 * Reports the symmetry partitions that were detected.
	 * The given partitions must not be mutated.
	 */
	public void detectedSymmetries(Set<IntSet> parts);
	
	/**
	 * Reports that bounds optimization is in progress (stage 2).
	 */
	public void optimizingBoundsAndFormula();
		
	/**
	 * Reports that the given declaration is being skolemized using the 
	 * given skolem relation.  The context list contains non-skolemizable 
	 * quantified declarations on which the given decl depends, in the order of declaration
	 * (most recent decl is last in the list).
	 */
	public void skolemizing(Decl decl, Relation skolem, List<Decl> context);
	
	/**
	 * Reports that the analysis of the given (optimized) formula
	 * and bounds is in stage 3.  The given bounds must not be mutated.
	 * @ensures bounds' = bounds
	 */
	public void translatingToBoolean(Formula formula, Bounds bounds);
	
	/**
	 * Reports that the analysis is in stage 4.
	 */
	public void generatingSBP();

	/**
	 * Reports that the given (optimized)
	 * circuit is being translated to CNF (stage 5 of the analysis).
	 */
	public void translatingToCNF(BooleanFormula circuit);
	
	/**
	 * Reports that the cnf generated in stage 6, consisting of the
	 * given number of variables and clauses, is being analyzed by
	 * a sat solver (stage 7 of the analysis).
	 */
	// [HASLab]
	public void solvingCNF(int step, int primaryVars, int vars, int clauses);
	
	/**
	 * TODO
	 */
	// [HASLab]
	public void reportLex(List<Entry<Relation, Tuple>> original,
			List<Entry<Relation, Tuple>> permuted);
	
	/**
	 * TODO
	 */
	// [HASLab] 
	public void debug(String debug);

	/**
	 * TODO
	 */
	// [HASLab] 
	public void warning(String warning);
	
	/**
	 * TODO
	 */
	// [HASLab]
	public void reportConfigs(int configs, int primaryVars, int vars, int clauses);

}
