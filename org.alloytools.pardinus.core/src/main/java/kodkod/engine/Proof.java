/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.util.nodes.Nodes;

/**
 * Contains a proof of unsatisfiability of a
 * given FOL formula.
 * 
 * @specfield log: TranslationLog // log of the translation of this.formula with respect to this.bounds
 */
public abstract class Proof {
	private final TranslationLog log;
	
	/**
	 * Constructs a new Proof of unsatisfiability for log.formula.
	 * @ensures this.log = log
	 */
	Proof(TranslationLog log) {
		this.log = log;
	}
	
	/**
	 * Minimizes the proof of this.log.formula's unsatisfiability
	 * using the specified proof reduction strategy.  The strategy
	 * argument is ignored (it can be null) if this.formula is 
	 * trivially unsatisfiable with respect to this.bounds.  In that
	 * case, the core is reduced using the trivial strategy
	 * that does one of the following: (1) if there is a 
	 * root that simplified to FALSE, sets the minimal core
	 * to that root; or (2) if not, then there must be two
	 * roots that translated to x and -x, where x is a boolean 
	 * literal, so we pick those two as the minimal core. 
	 * 
	 * <p><b>Note:</b> the core minimization is performed at the level of the 
	 * transformed formula, not the original formula if the problem was translated
	 * with a non-zero {@linkplain Options#coreGranularity() core granularity} setting.
	 * In other words, after this method has been called, {@linkplain #highLevelCore() highLevelCore()} 
	 * returns a map M such that M.keySet() is a minimal core with respect to this.log.bounds. In contrast,
	 * {@linkplain Nodes#allRoots(Formula, java.util.Collection) Nodes.roots(this.log.originalFormula, M.values())} is 
	 * unsatisfiable with respect this.log.originalBounds.  These formulas, however, do not necessarily form a 
	 * minimal core of this.log.originalFormula if the original problem was translated
	 * with a non-zero {@linkplain Options#coreGranularity() core granularity} setting.  </p>
	 * 
	 * @ensures minimizes the proof of this.log.formula's unsatisfiability
	 * using the specified proof reduction strategy (or the trivial 
	 * strategy if this.formula is trivially unsatisfiable with respect
	 * to this.bounds). 
	 * 
	 * @see kodkod.engine.satlab.ReductionStrategy
	 */
	public abstract void minimize(ReductionStrategy strategy);
	
	/**
	 * Returns an iterator over the {@link TranslationRecord log records} for the nodes
	 * that are in the unsatisfiable core of this.log.formula.   The record objects returned by the iterator are not 
	 * guaranteed to be immutable.  In particular, the state of a record object
	 * returned by <tt>next()</tt> is guaranteed to remain the same only until the
	 * subsequent call to <tt>next()</tt>.
	 * @return  an iterator over the {@link TranslationRecord log records} for the nodes
	 * that are in the unsatisfiable core of this.log.formula.
	 */
	public abstract Iterator<TranslationRecord> core() ;
	
	/**
	 * Returns a map whose key set is the unsatisfiable subset of the top-level conjunctions of this.log.formula
	 * as given by {@linkplain #core() this.core()}.  Each formula in the key set is mapped to the descendant of this.log.originalFormula
	 * from which it was derived by skolemization or by some other optimization.
	 * @return a map whose key set is the unsatisfiable subset of the top-level conjunctions of this.log.formula,
	 * as given by {@linkplain #core() this.core()}.  Each formula in the key set is mapped to the descendant of this.log.originalFormula
	 * from which it was derived by skolemization or by some other optimization.
	 * @see #minimize(ReductionStrategy)
	 */
	public abstract Map<Formula, Node> highLevelCore() ;
	
	/**
	 * Returns the log of the translation that resulted
	 * in this proof.
	 * @return log of the translation that resulted in this proof
	 */
	public final TranslationLog log() {
		return log;
	}
	
	/**
	 * Returns a string representation of this proof.
	 * @return a string representation of this proof.
	 * @see java.lang.Object#toString()
	 */
//	public String toString() {
//		final StringBuilder ret = new StringBuilder();
//		for(Formula f : highLevelCore()) {
//			ret.append(" ");
//			ret.append(f);
//			ret.append("\n");
//		}
//		return ret.toString();
//	}
	
}