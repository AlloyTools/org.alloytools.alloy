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

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.util.ints.IntSet;

/**
 * An implementation of the reporter interface that prints messages through a
 * SLF4J logger.
 * 
 * @author Nuno Macedo // [HASLab] additional reporting
 */
public class SLF4JReporter implements Reporter {
	
    private Logger LOGGER = LoggerFactory.getLogger(Reporter.class);
	
	/**
	 * Constructs a new instance of the ConsoleReporter.
	 */
	public SLF4JReporter() {}
	
	/**
	 * @see kodkod.engine.config.Reporter#generatingSBP()
	 */
	public void generatingSBP() {
		LOGGER.info("generating lex-leader symmetry breaking predicate ...");
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#skolemizing(kodkod.ast.Decl, kodkod.ast.Relation, java.util.List)
	 */
	public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {
		LOGGER.info("skolemizing " + decl + ": skolem relation=" + skolem + ", arity=" + skolem.arity());
	}

	/**
	 * @see kodkod.engine.config.Reporter#solvingCNF(int, int, int)
	 */
	public void solvingCNF(int step, int primaryVars, int vars, int clauses) {
		LOGGER.info("solving p cnf " + vars + " " + clauses);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#detectingSymmetries(kodkod.instance.Bounds)
	 */
	public void detectingSymmetries(Bounds bounds){
		LOGGER.info("detecting symmetries ...");
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#optimizingBoundsAndFormula()
	 */
	public void optimizingBoundsAndFormula() {
		LOGGER.info("optimizing bounds and formula (breaking predicate symmetries, inlining, skolemizing) ...");
	}

	/**
	 * @see kodkod.engine.config.Reporter#translatingToCNF(kodkod.engine.bool.BooleanFormula)
	 */
	public void translatingToCNF(BooleanFormula circuit) {
		LOGGER.info("translating to cnf ...");
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#translatingToBoolean(Formula, Bounds)
	 */
	public void translatingToBoolean(Formula formula, Bounds bounds) {
		if (Options.isDebug()) {
			debug("Final problem formula: "+formula);
			debug("Final problem bounds: "+bounds);
		}
		else
			LOGGER.info("translating to boolean ...");
	}

	/**
	 * @see kodkod.engine.config.Reporter#translatingToBoolean(Formula, Bounds)
	 */
	public void detectedSymmetries(Set<IntSet> parts) {
		LOGGER.info("detected " + parts.size() + " equivalence classes of atoms ...");
	}

	/**
	 * @see kodkod.engine.config.Reporter#reportLex(List, List)
	 */
	public void reportLex(List<Entry<Relation, Tuple>> _original,
			List<Entry<Relation, Tuple>> _permuted) {
		if (Options.isDebug())
			debug("lex: "+_original.toString() + " < " + _permuted.toString());
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#debug(String)
	 */
	public void debug(String debug) {
		if (Options.isDebug()) {
			if (debug.length() >= 320)
				LOGGER.debug(debug.substring(0, 320)+"...");
			else
				LOGGER.debug(debug);
		}
	}

	/**
	 * @see kodkod.engine.config.Reporter#warning(String)
	 */
	public void warning(String warning) {
		LOGGER.warn(warning);
	}

	/**
	 * @see kodkod.engine.config.Reporter#reportConfigs(int)
	 */
	public void reportConfigs(int configs, int vars, int pvars, int clauses) {
		if (Options.isDebug())
			debug("found at least "+configs+" configs...");
	}

}
