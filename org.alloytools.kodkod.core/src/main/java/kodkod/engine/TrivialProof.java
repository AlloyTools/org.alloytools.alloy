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

import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.RelationPredicate;
import kodkod.ast.Variable;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.engine.fol2sat.RecordFilter;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.instance.TupleSet;
import kodkod.util.collections.IdentityHashSet;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * A proof of unsatisfiability for a trivially unsatisfiable formula.
 * A formula is considered trivally unsatisfiable if its unsatisfiability
 * is discovered through translation alone.
 *  
 * @author Emina Torlak
 */
final class TrivialProof extends Proof {
	private Map<Formula,Node> coreRoots;
	private RecordFilter coreFilter;
	
	/**
	 * Constructs a proof of unsatisfiability for the trivially unsatisfiable
	 * formula whose translation is recorded in the given log.
	 * @requires log != null
	 * @ensures this.formula' = log.formula
	 */
	TrivialProof(TranslationLog log) {
		super(log);
		this.coreFilter = null;
		this.coreRoots = null;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.Proof#core()
	 */
	public final Iterator<TranslationRecord> core() { 
		if (coreFilter==null) {
			coreFilter = new RecordFilter() {
				final Set<Node> coreNodes = NodePruner.relevantNodes(log(),  coreRoots==null ? log().roots() : coreRoots.keySet());
				public boolean accept(Node node, Formula translated, int literal, Map<Variable, TupleSet> env) {
					return coreNodes.contains(translated) ;
				}
			};
		}
		return log().replay(coreFilter); 
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.Proof#highLevelCore()
	 */
	public final Map<Formula,Node> highLevelCore() {
		if (coreRoots==null) { 
			final Iterator<TranslationRecord> itr = core();
			final Set<Formula> roots = log().roots();
			coreRoots = new LinkedHashMap<Formula,Node>();
			while( itr.hasNext() ) {
				TranslationRecord rec = itr.next();
				if (roots.contains(rec.translated()))
					coreRoots.put(rec.translated(), rec.node());
			}
			coreRoots = Collections.unmodifiableMap(coreRoots);
		}
		return coreRoots;
	}
	
	/**
	 * Minimizes the current core using the trivial strategy
	 * that does one of the following: (1) if there is a 
	 * root that simplified to FALSE, sets the minimal core
	 * to that root; or (2) if not, there must be two
	 * roots that translated to x and -x, where x is a boolean 
	 * literal, so we pick those two as the minimal core.
	 * The strategy argument is ignored (it can be null).
	 * @see Proof#minimize(ReductionStrategy)
	 */
	@Override
	public void minimize(ReductionStrategy strategy) {	
		final Map<Formula, int[]> rootLits = new LinkedHashMap<Formula,int[]>();
		final Map<Formula, Node> rootNodes = new LinkedHashMap<Formula, Node>();
		final Set<Formula> roots = log().roots();
		
		for(Iterator<TranslationRecord> itr = core(); itr.hasNext();) { 
			final TranslationRecord rec = itr.next();
			if (roots.contains(rec.translated())) { 
				// simply record the most recent output value for each formula:
				// this is guaranteed to be the final output value for that 
				// formula because of the translation log guarantee that the
				// log is replayed in the order of translation:  i.e. a child's
				// output value is always recorded before the parent's
				int[] val = rootLits.get(rec.translated());
				if (val==null) { 
					val = new int[1]; 
					rootLits.put(rec.translated(), val);
				}
				val[0] = rec.literal();
				rootNodes.put(rec.translated(), rec.node());
			}
		}
		
		final SparseSequence<Formula> lits = new TreeSequence<Formula>();
		for(Map.Entry<Formula,int[]> entry : rootLits.entrySet()) { 
			final int lit = entry.getValue()[0];
			if (lit==-Integer.MAX_VALUE) { 
				coreRoots = Collections.singletonMap(entry.getKey(), rootNodes.get(entry.getKey()));
				break;
			} else if (lits.containsIndex(-lit)) { 
				final Formula f0 = lits.get(-lit);
				final Formula f1 = entry.getKey();
				coreRoots = new LinkedHashMap<Formula, Node>(3);
				coreRoots.put(f0, rootNodes.get(f0));
				coreRoots.put(f1, rootNodes.get(f1));
				coreRoots = Collections.unmodifiableMap(coreRoots);
				break;
			} else {
				lits.put(lit, entry.getKey());
			}
		}
		
		coreFilter = null;
		assert coreRoots.size()==1 && rootLits.get(coreRoots.keySet().iterator().next())[0]==-Integer.MAX_VALUE || coreRoots.size()==2;
	}

	/**
	 * Given a translation log for a trivially unsatisfiable formula, finds the nodes 
	 * necessary for proving the formula's unsatisfiability.  Instances of this
	 * visitor should be constructed and applied using the {@linkplain #relevantNodes(TranslationLog)}
	 * 
	 * @specfield log: TranslationLog
	 * @author Emina Torlak
	 */
	private static final class NodePruner extends AbstractVoidVisitor {
		private final Set<Node> visited, relevant;
		private final Map<Formula,Boolean> constNodes;
		
		/**
		 * Constructs a proof finder for the given log.
		 * @ensures this.log' = log
		 */
		NodePruner(TranslationLog log) {
			visited = new IdentityHashSet<Node>();
			relevant = new IdentityHashSet<Node>();
						
			final RecordFilter filter = new RecordFilter() {
				public boolean accept(Node node, Formula translated, int literal, Map<Variable, TupleSet> env) {
					return env.isEmpty();
				}	
			};
			
			constNodes = new LinkedHashMap<Formula,Boolean>();
			for(Iterator<TranslationRecord> itr = log.replay(filter); itr.hasNext(); ) { 
				TranslationRecord rec = itr.next();
				int lit = rec.literal();
				if (Math.abs(lit) != Integer.MAX_VALUE) { 
					constNodes.remove(rec.translated());
				} else if (lit==Integer.MAX_VALUE) { 
					constNodes.put(rec.translated(), Boolean.TRUE);
				} else {
					constNodes.put(rec.translated(), Boolean.FALSE);
				}
			}
		}
		
		/**
		 * Returns the nodes necessary for proving the trivial unsatisfiability of log.formula.
		 * @requires some r: log.records | r.node = log.formula && r.literal = BooleanConstant.FALSE.label
		 * @requires highLevelCore in log.roots() and unsatisfiable(highLevelCore, log.bounds, log.options)
		 * @return nodes necessary for proving the trivial unsatisfiability of log.formula.
		 */
		static Set<Node> relevantNodes(TranslationLog log, Set<Formula> highLevelCore) {
			final NodePruner finder = new NodePruner(log);
			for(Formula root : highLevelCore) {
				if (!finder.isTrue(root)) {
					root.accept(finder);		
				}
			}
			return finder.relevant;
		}
		
		/**
		 * Returns true if the given node has been visited before.
		 * @ensures this.visited' = this.visited + n
		 * @return n in this.visited 
		 */
		@Override
		protected boolean visited(Node n) {
			return !visited.add(n);
		}
		
		/**
		 * Returns true if the node was simplified to TRUE during translation.
		 * @return some r: this.log.records | r.node = node && no r.env && r.literal = BooleanConstant.TRUE.label
		 */
		final boolean isTrue(Node node) { return constNodes.get(node)==Boolean.TRUE; }
				
		public void visit(Decl decl) { 
			if (visited(decl)) return;
			relevant.add(decl);
		}
		
		public void visit(QuantifiedFormula quantFormula) { 
			if (visited(quantFormula)) return;
			relevant.add(quantFormula);
		}
		
		public void visit(ComparisonFormula compFormula) { 
			if (visited(compFormula)) return;
			relevant.add(compFormula); 	
		}
		public void visit(MultiplicityFormula multFormula) { 
			if (visited(multFormula)) return;
			relevant.add(multFormula);	
		}
		public void visit(RelationPredicate pred) { 
			if (visited(pred)) return;
			relevant.add(pred); 	
		}
		public void visit(IntComparisonFormula intComp) { 
			if (visited(intComp)) return;
			relevant.add(intComp); 	
		}
		
		public void visit(ConstantFormula formula) { 
			relevant.add(formula);
		}
		
		/**
		 * If the argument node has been been visited, adds it to this.relevant and visits its child.
		 */
		public void visit(NotFormula not) {
			if (visited(not)) return; 
			relevant.add(not);
			not.formula().accept(this);
		}
		
	
		/**
		 * If this formula should be visited, then we visit its children only
		 * if they could have contributed to the unsatisfiability of the top-level
		 * formula.  For example, let binFormula = "p && q", binFormula simplified
		 * to FALSE, p simplified to FALSE and q was not simplified, then only p 
		 * should be visited since p caused binFormula's reduction to FALSE.
		 */
		public void visit(BinaryFormula binFormula) {
			if (visited(binFormula)) return;
			relevant.add(binFormula);
			
			final Formula l = binFormula.left(), r = binFormula.right();
			final Boolean lval = constNodes.get(l), rval = constNodes.get(r);
			final boolean lvisit, rvisit;
			
			switch(binFormula.op()) {
			case AND : 
				lvisit = (lval==Boolean.FALSE || (lval==null && rval!=Boolean.FALSE));
				rvisit = (rval!=Boolean.TRUE && lval!=Boolean.FALSE);
				break;
			case OR :
				lvisit = (lval==Boolean.TRUE || (lval==null && rval!=Boolean.TRUE));
				rvisit = (rval!=Boolean.FALSE && lval!=Boolean.TRUE);
				break;
			case IMPLIES: // !l || r
				lvisit = (lval==Boolean.FALSE || (lval==null && rval!=Boolean.TRUE));
				rvisit = (rval!=Boolean.FALSE && lval!=Boolean.FALSE);
				break;
			case IFF: // (!l || r) && (l || !r) 
				lvisit = rvisit = true;
				break;
			default :
				throw new IllegalArgumentException("Unknown operator: " + binFormula.op());
			}	
			
			if (lvisit) { l.accept(this); }
			if (rvisit) { r.accept(this); }
		}
		
		/**
		 * If this formula should be visited, then we visit its children only
		 * if they could have contributed to the unsatisfiability of the top-level
		 * formula.  For example, let binFormula = "p && q", binFormula simplified
		 * to FALSE, p simplified to FALSE and q was not simplified, then only p 
		 * should be visited since p caused binFormula's reduction to FALSE.
		 */
		public void visit(NaryFormula formula) {
			if (visited(formula)) return;
			relevant.add(formula);
			
			final Boolean val = constNodes.get(formula);
			final Boolean cancel;
			
			switch(formula.op()) { 
			case AND : cancel = Boolean.FALSE; break;
			case OR  : cancel = Boolean.TRUE; break;
			default  : throw new IllegalArgumentException("Unknown nary operator: " + formula.op());
			}
			
			final Boolean iden = Boolean.valueOf(!cancel);
			if (val!=iden) {
				for(Formula child : formula) { 
					if (constNodes.get(child)==cancel) {
						child.accept(this);
						return;
					}
				}
				for(Formula child : formula) { 
					if (constNodes.get(child)!=iden)	{ 
						child.accept(this); 
					} 
				}
				return;
			} 
				
			for(Formula child : formula) { child.accept(this); }
		}
	}
	
}