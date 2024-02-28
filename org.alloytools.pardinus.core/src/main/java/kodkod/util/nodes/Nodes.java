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
package kodkod.util.nodes;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;
import kodkod.util.collections.IdentityHashSet;

/**
 * Provides utility methods for extracting roots (top-level) conjuncts
 * of Kodkod formulas
 * 
 * @author Emina Torlak
 */
public final class Nodes {
	private Nodes() {}
	
	/**
     * Returns the roots of the given formula.
     * In other words, breaks up the given formula into its conjunctive 
     * components, {f0, ..., fk}, 
     * such that, for all 0<=i<=k, f<sub>i</sub> is not a conjunction  and
     * [[f0 && ... && fk]] <=> [[formula]].  
     * @return subformulas, {f0, ..., fk}, of the given formula such that, for all 0<=i<=k, 
     * f<sub>i</sub> is not a conjuction and [[f0 && ... && fk]] <=> [[formula]].    
     */
	public static Set<Formula> roots(Formula formula) {
	
    	final List<Formula> formulas = new LinkedList<Formula>();
		formulas.add(formula);
		
		final ListIterator<Formula> itr = formulas.listIterator();
		while(itr.hasNext()) {
			final Formula f = itr.next();
			if (f instanceof BinaryFormula) {
				final BinaryFormula bin = (BinaryFormula) f;
				if (bin.op()==FormulaOperator.AND) {
					itr.remove();
					itr.add(bin.left());
					itr.add(bin.right());
					itr.previous();
					itr.previous();
				}
			} else if (f instanceof NaryFormula) { 
				final NaryFormula nf = (NaryFormula) f;
				if (nf.op()==FormulaOperator.AND) { 
					itr.remove();
					for(Formula child : nf) { 
						itr.add(child);
					}
					for(int i = nf.size(); i>0; i--) { 
						itr.previous();
					}
				}
			}
		}
		
		return new LinkedHashSet<Formula>(formulas);
	}
	
	/**
	 * Returns an unmodifiable set consisting of the children of the given formula, if the formula is a binary or an nary conjunction.  Otherwise
	 * returns a singleton set containing the formula itself.
	 * @return  an unmodifiable set consisting of children of the given formula, if the formula is a binary or an nary conjunction.  Otherwise
	 * returns a singleton set containing the formula itself.
	 */
	public static Set<Formula> conjuncts(Formula formula) { 
		if (formula instanceof BinaryFormula) { 
			final BinaryFormula bin = (BinaryFormula) formula;
			if (bin.op()==FormulaOperator.AND) {
				final Formula left = bin.left(), right = bin.right();
				if (left==right) return Collections.singleton(left);
				else return new AbstractSet<Formula>() {
					@Override
					public boolean contains(Object o) { return left==o || right==o; }
					@Override
					public Iterator<Formula> iterator() { return Containers.iterate(left, right); }
					@Override
					public int size() { return 2;	}
					
				};
			}
		} else if (formula instanceof NaryFormula) { 
			final NaryFormula nf = (NaryFormula) formula;
			if (nf.op()==FormulaOperator.AND) { 
				final LinkedHashSet<Formula> children = new LinkedHashSet<Formula>(1+(nf.size()*4)/3);
				for(Formula child : nf) { children.add(child); }
				return Collections.unmodifiableSet(children);
			}
		} 
		
		return Collections.singleton(formula);
		
	}
	
	/**
	 * Returns a minimal subset of {@linkplain #roots(Formula) roots} of the given formula such that all nodes in the given collection
	 * are reachable from those roots.  The returned subset is a local minimum in that none of its members can be removed without leaving
	 * some node in the descendants set unreachable from the remaining roots.
	 * @requires descendants in formula.*components
	 * @return { s: Set<Formula> | s.elements in roots(formula) and descendants in s.elements.*components and 
	 * 				no s': Set<Formula> | s.containsAll(s') and s'.size()<s.size() and descendants in s.elements.*components }
	 * @throws IllegalArgumentException  descendants !in formula.*components
	 */
	public static Set<Formula> minRoots(Formula formula, Collection<? extends Node> descendants) { 
		
		final Set<Node> desc = new IdentityHashSet<Node>(descendants);
		final VoidVisitor visitor = new AbstractVoidVisitor() {
			final Set<Node> visited = new IdentityHashSet<Node>();
			@Override
			protected boolean visited(Node n) {
				if (visited.add(n)) {
					desc.remove(n);
					return false;
				}
				return true;
			}
		};
		
		final Set<Formula> roots = new LinkedHashSet<Formula>();
		for(Formula root : roots(formula)) { 
			final int size = desc.size();
			root.accept(visitor);
			if (desc.size()<size) { roots.add(root); }
			if (desc.isEmpty()) { break; }
		}
		
		if (!desc.isEmpty()) 
			throw new IllegalArgumentException("descendants !in formula.*components: formula="+formula+" ; descendants="+descendants);
		
		return roots;
	}
	
	/**
	 * Returns all {@linkplain #roots(Formula) roots} of the given formula such that a node in the given collection
	 * is reachable from that root.
	 * @return { r: roots(formula) | some r.*components & descendants.elements }
	 */
	@SuppressWarnings("unchecked")
	public static Set<Formula> allRoots(Formula formula, Collection<? extends Node> descendants) { 
		final Set<Node> desc = new IdentityHashSet<Node>(descendants);
		final AbstractDetector detector = new AbstractDetector(Collections.EMPTY_SET) {
			protected Boolean lookup(Node n) {
				return desc.contains(n) ? Boolean.TRUE : cache.get(n);
			}
			protected Boolean cache(Node n, boolean val) {
				final Boolean ret = Boolean.valueOf(val);
				cache.put(n, ret);
				return ret;
			}		
		};
		
		final Set<Formula> roots = new LinkedHashSet<Formula>();
		for(Formula root : roots(formula)) { 
			if (root.accept(detector)) { 
				roots.add(root);
			}
		}
	
		return roots;
	}
	
}
