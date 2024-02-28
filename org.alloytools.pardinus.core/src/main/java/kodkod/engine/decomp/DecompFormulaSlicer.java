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
package kodkod.engine.decomp;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.fol2sat.FormulaFlattener;
import kodkod.engine.fol2sat.RelationCollector;
import kodkod.instance.PardinusBounds;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Slices a first-order logic formula into a pair of conjuncts given a set of
 * variables as the slicing criteria, intended to be used during decomposed
 * model finding. Uses a {@link FormulaFlattener formula flattener} to reduce to
 * NNF and flatten conjuncts, which are then filtered according to the set of
 * variables.
 * 
 * The {@link PardinusBounds bounds} with decomposed information. If the problem
 * is not integrated (still at the first stage), then only set of partial
 * variables occurs in the bounds. If integrated, all variables occur in the
 * bounds, and only those still not constant are considered for the second
 * stage. If the process is at the second stage and every variable is already
 * constant returns the whole formula (probably a case of trivial solution
 * iteration).
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class DecompFormulaSlicer {

	/**
	 * Slices the conjuncts of a formula into two, depending on the variables
	 * selected for the partial problem, as defined in the bounds of the
	 * problem. Considers whether the bounds are already integrated to retrieve
	 * the relevant variables. 
	 *
	 * @param formula
	 *            the formula to be sliced.
	 * @param bounds
	 *            the bounds containing information regarding the selected
	 *            variables.
	 * @return two conjuncts of the formula according to the selected variables.
	 */
	public static Entry<Formula, Formula> slice(Formula formula, PardinusBounds bounds) {
		Set<Relation> partials = new HashSet<Relation>();
		if (bounds.integrated()) {
			for (Relation r : bounds.relations())
				// new relation, probably from trivial iteration
				if (!bounds.amalgamated.relations().contains(r)) {} 
				// still symbolic, not partial
				else if (bounds.lowerSymbBound(r) != null) {} 
				// if exactly bound, was part of the partial problem
				else if (bounds.amalgamated.upperBound(r).size() == bounds.amalgamated.lowerBound(r).size())
					partials.add(r);
		} else {
			// if not integrated, bounds are the partial
			partials = bounds.relations();
		}
		return slice(formula,partials);
	}
		
	public static Entry<Formula, Formula> slice(Formula formula, Set<Relation> partials) {

		// converts to NNF and flattens the formula
		AnnotatedNode<Formula> flat = FormulaFlattener.flatten(
				AnnotatedNode.annotateRoots(formula), false);
		final Formula form = flat.node();
		List<Formula> f2 = new ArrayList<Formula>();
		List<Formula> f1 = new ArrayList<Formula>();
		RelationCollector col = new RelationCollector(flat.sharedNodes());
		// select the appropriate conjuncts
		if (form instanceof BinaryFormula
				&& ((BinaryFormula) form).op() == FormulaOperator.AND) {
			Set<Relation> rsl = ((BinaryFormula) form).left().accept(col);
			Set<Relation> rsr = ((BinaryFormula) form).right().accept(col);
			(partials.containsAll(rsl)?f1:f2).add(((BinaryFormula) form).left());
			(partials.containsAll(rsr)?f1:f2).add(((BinaryFormula) form).right());
		} else if (form instanceof NaryFormula
				&& ((NaryFormula) form).op() == FormulaOperator.AND) {
			Iterator<Formula> it = ((NaryFormula) form).iterator();
			while (it.hasNext()) {
				Formula f = it.next();
				Set<Relation> rs = f.accept(col);
				if (partials.containsAll(rs))
					f1.add(f);
				else
					f2.add(f);
			}
		} else {
			Set<Relation> rs = form.accept(col);
			if (partials.containsAll(rs))
				f1.add(form);
			else 
				f2.add(form);
		}
		return new SimpleEntry<Formula, Formula>(NaryFormula.and(f1), NaryFormula.and(f2));
	}
	
	// TODO: temporal slicing will fail if temporal formulas over static relations
}
