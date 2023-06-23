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
 * An implementation of the reporter interface that prints messages
 * to the standard output stream.
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] additional reporting
 */
public final class ConsoleReporter implements Reporter {
	
	/**
	 * Constructs a new instance of the ConsoleReporter.
	 */
	public ConsoleReporter() {}
	
	/**
	 * @see kodkod.engine.config.Reporter#generatingSBP()
	 */
	public void generatingSBP() {
		System.out.println("generating lex-leader symmetry breaking predicate ...");
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#skolemizing(kodkod.ast.Decl, kodkod.ast.Relation, java.util.List)
	 */
	public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {
		System.out.println("skolemizing " + decl + ": skolem relation=" + skolem + ", arity=" + skolem.arity());
	}

	/**
	 * @see kodkod.engine.config.Reporter#solvingCNF(int, int, int)
	 */
	// [HASLab]
	public void solvingCNF(int step, int primaryVars, int vars, int clauses) {
		System.out.println("solving p cnf " + vars + " " + clauses);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#detectingSymmetries(kodkod.instance.Bounds)
	 */
	public void detectingSymmetries(Bounds bounds){
		System.out.println("detecting symmetries ...");
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#detectedSymmetries(java.util.Set)
	 */
	public void detectedSymmetries(Set<IntSet> parts) {
		System.out.println("detected " + parts.size() + " equivalence classes of atoms ...");
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#optimizingBoundsAndFormula()
	 */
	public void optimizingBoundsAndFormula() {
		System.out.println("optimizing bounds and formula (breaking predicate symmetries, inlining, skolemizing) ...");
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#translatingToBoolean(kodkod.ast.Formula, kodkod.instance.Bounds)
	 */
	public void translatingToBoolean(Formula formula, Bounds bounds) {
		System.out.println("translating to boolean ...");
	}

	/**
	 * @see kodkod.engine.config.Reporter#translatingToCNF(kodkod.engine.bool.BooleanFormula)
	 */
	public void translatingToCNF(BooleanFormula circuit) {
		System.out.println("translating to cnf ...");
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#reportLex(List, List)
	 */
	// [HASLab]
	public void reportLex(List<Entry<Relation, Tuple>> original,
			List<Entry<Relation, Tuple>> permuted) {}
	
	/**
	 * @see kodkod.engine.config.Reporter#debug(String)
	 */
	// [HASLab]
	public void debug(String debug) {
		System.out.println(debug);
	}

	/**
	 * @see kodkod.engine.config.Reporter#warning(String)
	 */
	// [HASLab]
	public void warning(String warning) {
		System.out.println(warning);
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#reportConfigs(int)
	 */
	// [HASLab]
	public void reportConfigs(int configs, int vars, int pvars, int clauses) {
		System.out.println("found at least "+configs+" configs...");
	}
	
	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "ConsoleReporter";
	}

}
