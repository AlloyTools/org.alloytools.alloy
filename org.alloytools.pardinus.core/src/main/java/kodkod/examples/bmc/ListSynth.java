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

import java.util.ArrayList;

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
import kodkod.instance.Universe;

/**
 * Synthesis demo.
 * 
 * @author Emina Torlak
 *
 */
public class ListSynth extends ListEncoding {
	private final Relation 	hole,
							headStx, nearNode0Stx, midNode0Stx, farNode0Stx;
	
	ListSynth() {
		// introduce relations that we'll use for reflection; that is, a relation
		// that represents the syntax "this.head", "nearNode0", etc.
		// also introduce a relation that map each piece of syntax to its meaning.

		headStx = Relation.unary("\"head\"");
		nearNode0Stx = Relation.unary("\"nearNode0\"");
		midNode0Stx = Relation.unary("\"midNode0\"");
		farNode0Stx = Relation.unary("\"farNode0\"");
		
		// represents the hole for "farNode0" in "next0 = update(next, nearNode0 -> farNode0)"
		hole = Relation.unary("\"??\""); 
	}
	
	Expression meaning() {
		return Expression.union(
				nil.product(nil), 
				headStx.product(thisList.join(head)),
				nearNode0Stx.product(nearNode0()), 
				midNode0Stx.product(midNode0()),
				farNode0Stx.product(farNode0()));
	}
	
	Expression next0()  {
		return next.override(nearNode0().product(hole.join(meaning()))); 		// next0 := update(next, nearNode0 -> ??.meaning)
	}
	
	Formula synthSpec() {
		// make sure that our hole is a singleton
		return Formula.and(
				pre(), loopGuard(), post(), hole.one());
	}
	
	Bounds synthBounds(int size) {
		final Bounds b = bounds(size);
		final ListCheck checker = new ListCheck();
		final Instance cex = checker.check(size).instance();
		assert cex != null;
		final TupleFactory t = b.universe().factory();
		
		b.bound(hole, t.setOf("nil", headStx, nearNode0Stx, midNode0Stx, farNode0Stx));
		
		
		b.boundExactly(headStx, t.setOf(headStx));
		b.boundExactly(nearNode0Stx, t.setOf(nearNode0Stx));
		b.boundExactly(midNode0Stx, t.setOf(midNode0Stx));
		b.boundExactly(farNode0Stx, t.setOf(farNode0Stx));
		
		b.boundExactly(next, copyFrom(t, cex.tuples(checker.next)));
		b.boundExactly(head, copyFrom(t, cex.tuples(checker.head)));
		b.boundExactly(data, copyFrom(t, cex.tuples(checker.data)));
		b.boundExactly(thisList, copyFrom(t, cex.tuples(checker.thisList)));

		return b;
	}
	
	Universe universe(int size) {
		final ArrayList<Object> elts = new ArrayList<Object>(2 + size * 2);
		elts.add("l0");
		for(int i = 0; i < size; i++) { elts.add("n" + i); }
		for(int i = 0; i < size; i++) { elts.add("s" + i); }
		elts.add("nil");
		elts.add(headStx); // the syntax relations will represent themselves in the universe
		elts.add(nearNode0Stx);
		elts.add(midNode0Stx);
		elts.add(farNode0Stx);
		return new Universe(elts);
	}
	
	Solution synth(int size) {
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		return solver.solve(synthSpec(), synthBounds(size));
	}
	
	private void showSynth(int size) {
		final Solution sol = synth(size);
		System.out.println("************ SYNTHESIZE REVERSE REPAIR FOR " + size + " NODES ************");
		System.out.println(sol.outcome());
		System.out.println();
		System.out.println(sol.stats());
		System.out.println();
		ListViz.printInstance(this, sol.instance());
		ListViz.printStateGraph("synth-pre", this, sol.instance(), State.PRE);
		ListViz.printStateGraph("synth-post", this, sol.instance(), State.POST);
		System.out.println("\n-----------Syntax-----------");
		System.out.println(hole + " = " + sol.instance().tuples(hole));
	}
	
	public static void main(String[] args) {
		ListSynth enc = new ListSynth();
		//ListViz.printEncoding(enc);
		enc.showSynth(3);
	}
	
}
