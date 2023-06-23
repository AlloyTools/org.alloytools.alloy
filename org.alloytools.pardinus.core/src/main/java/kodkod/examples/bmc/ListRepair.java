/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.examples.bmc;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.bmc.ListViz.State;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;

/**
 * Data structure repair demo.
 * 
 * @author Emina Torlak
 */
public class ListRepair extends ListEncoding {
	final Relation next3, head0;
	
	ListRepair() {
		
		next3 = Relation.binary("next3");						// next3 = free variable
		head0 = Relation.binary("head0");						// head0 = free variable
	}

	Expression next3() { return next3; }
	Expression head0() { return head0; }
	
	Formula repairSpec() {
		return Formula.and(pre(), post());
	}
	
	Bounds repairBounds(int size) { 
		final Bounds b = bounds(size);
		final ListCheck checker = new ListCheck();
		final Instance cex = checker.check(size).instance();
		assert cex != null;
		final TupleFactory t = b.universe().factory();
		b.bound(next3, b.upperBound(next));
		b.bound(head0, b.upperBound(head));
		b.boundExactly(next, copyFrom(t, cex.tuples(checker.next)));
		b.boundExactly(head, copyFrom(t, cex.tuples(checker.head)));
		b.boundExactly(data, copyFrom(t, cex.tuples(checker.data)));
		b.boundExactly(thisList, copyFrom(t, cex.tuples(checker.thisList)));
		return b;
	}
	
	Solution repair(int size) {
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		return solver.solve(repairSpec(), repairBounds(size));
	}
	
	private void showRepair(int size) {
		final Solution sol = repair(size);
		System.out.println("************ REPAIR REVERSE FOR " + size + " NODES ************");
		System.out.println(sol.outcome());
		System.out.println();
		System.out.println(sol.stats());
		System.out.println();
		ListViz.printInstance(this, sol.instance());
		ListViz.printStateGraph("repair-pre", this, sol.instance(), State.PRE);
		ListViz.printStateGraph("repair-post", this, sol.instance(), State.POST);

	}
	
	public static void main(String[] args) {
		ListRepair enc = new ListRepair();
		//ListViz.printEncoding(enc);
		enc.showRepair(3);
	}
	
}
