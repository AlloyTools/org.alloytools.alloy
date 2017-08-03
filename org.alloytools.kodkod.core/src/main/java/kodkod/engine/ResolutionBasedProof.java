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

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Variable;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.engine.fol2sat.RecordFilter;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.SATProver;
import kodkod.engine.ucore.StrategyUtils;
import kodkod.instance.TupleSet;
import kodkod.util.collections.IdentityHashSet;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;

/**
 * A proof of unsatisfiability based on a {@linkplain ResolutionTrace resolution trace} produced
 * by a {@linkplain SATProver SATProver}.
 * 
 * @author Emina Torlak
 */
final class ResolutionBasedProof extends Proof {
	private SATProver solver;
	private RecordFilter coreFilter;
	private Map<Formula,Node> coreRoots;
	
	/**
	 * Constructs a new ResolutionRefutation that will extract the 
	 * unsatisfiable core for log.formula from the given solver.  
	 * @requires solver.solve() has been called and it returned false.
	 * @requires log.formula is the formula whose translation
	 * resulted in the given SATProver
	 * @ensures this.formula' = log.formula
	 */
	ResolutionBasedProof(SATProver solver, TranslationLog log) {
		super(log);
		this.solver = solver;
		this.coreFilter = null;
		this.coreRoots = null;
	}
	
	/**
	 * Returns the connected core based on the given set of 
	 * core variables.  
	 * @requires coreVar = StrategyUtils.coreVars(solver.proof());
	 * @return let formulas = (this.log.records[int] & literal.{i: int | abs(i) in coreVars}).formula |
	 *  	   connected = {f: formulas  | some s: set coreNodes | f + this.log.formula in s and (s - this.log.formula).~components in s } 
	 */
	private Set<Formula>  connectedCore(final IntSet coreVars) {
		final Set<Formula> coreNodes = new IdentityHashSet<Formula>();
		final RecordFilter filter = new RecordFilter() {
			public boolean accept(Node node, Formula translated, int literal, Map<Variable,TupleSet> env) {
				return coreVars.contains(StrictMath.abs(literal));
			}
		};
		for(Iterator<TranslationRecord> itr = log().replay(filter); itr.hasNext(); ) {
			coreNodes.add(itr.next().translated());
		}
		final Set<Formula> connected = new IdentityHashSet<Formula>();
		final AbstractVoidVisitor traverser = new AbstractVoidVisitor() {
			final Set<Node> visited = new IdentityHashSet<Node>();
			/**
			 * Returns true if the given node has been visited before or if 
			 * it is not contained in this.nodes set.  Otherwise adds 
			 * the node to the connected set and returns false.
			 * @ensures this.visited' = this.visited + n
			 * @ensures n !in this.visited && n in coreNodes => 
			 *  connected' = connected + n else connected' = connected
			 * @return n in visited || n !in coreNodes
			 */
			protected boolean visited(Node n) {
				if (visited.add(n) && coreNodes.contains(n)) {
					connected.add((Formula)n);
					return false;
				}
				return true;
			}
		};
		for(Formula root: log().roots()) {
			root.accept(traverser);
		}
		return connected;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.Proof#core()
	 */
	public final Iterator<TranslationRecord> core() { 
		if (coreFilter == null) {
			coreFilter = new RecordFilter() {
				final IntSet coreVariables = StrategyUtils.coreVars(solver.proof());
				final Set<Formula> coreNodes = connectedCore(coreVariables);
				public boolean accept(Node node, Formula translated, int literal, Map<Variable,TupleSet> env) {
					return coreNodes.contains(translated) && coreVariables.contains(StrictMath.abs(literal));
				}
			};
		}
		return log().replay(coreFilter); 
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.Proof#highLevelCore()
	 */
	public final Map<Formula, Node> highLevelCore() {
		if (coreRoots == null) { 
			final RecordFilter unitFilter = new RecordFilter() {
				final IntSet coreUnits = StrategyUtils.coreUnits(solver.proof());
				final Set<Formula> roots = log().roots();
				public boolean accept(Node node, Formula translated, int literal, Map<Variable, TupleSet> env) {
					return roots.contains(translated) && coreUnits.contains(Math.abs(literal));
				}
				
			};
			coreRoots = new LinkedHashMap<Formula, Node>();
			final IntSet seenUnits = new IntTreeSet();
			for(Iterator<TranslationRecord> itr = log().replay(unitFilter); itr.hasNext(); ) {
				// it is possible that two top-level formulas have identical meaning,
				// and are represented with the same core unit; in that case, we want only
				// one of them in the core.
				final TranslationRecord rec = itr.next();
				if (seenUnits.add(rec.literal())) {
					coreRoots.put(rec.translated(), rec.node());
				}  
			}
			coreRoots = Collections.unmodifiableMap(coreRoots);
		}
		return coreRoots;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.Proof#minimize(kodkod.engine.satlab.ReductionStrategy)
	 */
	public void minimize(ReductionStrategy strategy) {
		solver.reduce(strategy);
		coreFilter = null;
		coreRoots = null;
	}
}