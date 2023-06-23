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

import java.util.Collections;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Fault localization demo.
 * 
 * @author Emina Torlak
 *
 */
public class ListDebug extends ListEncoding {
	private final Relation 	head0, next0, next1, next3, 
							nearNode0, nearNode1, 
							midNode0, midNode1, 
							farNode0, farNode1;
	
	ListDebug() {
		
		// introduce extra degrees of freedom at potential repair points.
		// we consider everything except phi nodes as potential repair points.
		
		nearNode0 = Relation.unary("nearNode0");	 
		midNode0 = Relation.unary("midNode0");	 
		farNode0 = Relation.unary("farNode0");	 

		next0 = Relation.binary("next0"); 	 
		next1 = Relation.binary("next1");	 
		nearNode1= Relation.unary("nearNode1");	 
		midNode1 = Relation.unary("midNode1");	 
		farNode1 = Relation.unary("farNode1");	 
		
		next3 = Relation.binary("next3");	 
		head0 = Relation.binary("head0");	 
	}
	
	Expression nearNode0() { return nearNode0; } 
	Expression midNode0()  { return midNode0; }		 
	Expression farNode0()  { return farNode0; }	 
	
	Expression next0()     { return next0; }	 

	Expression next1()     { return next1; }	 
	Expression nearNode1() { return nearNode1; }	 
	Expression midNode1()  { return midNode1; } 
	Expression farNode1()  { return farNode1; }	 
		 							
	Expression next3()     { return next3; }	 
	Expression head0()     { return head0; }	 
	
	Formula debugSpec() {
		// connect each repair variable with its semantics
		return Formula.and(
				pre(), loopGuard(), post(),
				nearNode0.eq(super.nearNode0()),
				midNode0.eq(super.midNode0()),
				farNode0.eq(super.farNode0()),
				next0.eq(super.next0()),
				next1.eq(super.next1()),
				nearNode1.eq(super.nearNode1()),
				midNode1.eq(super.midNode1()),
				farNode1.eq(super.farNode1()),
				next3.eq(super.next3()),
				head0.eq(super.head0()));
	}
	
	Bounds debugBounds(int size) { 
		final Bounds b = bounds(size);
		final ListRepair repairer = new ListRepair();
		final Instance cex = repairer.repair(size).instance();
		assert cex != null;
		
		final TupleFactory t = b.universe().factory();
		final TupleSet nodeOrNil = t.noneOf(1);
		nodeOrNil.addAll(b.upperBound(node));
		nodeOrNil.addAll(b.upperBound(nil));
		
		b.bound(nearNode0, nodeOrNil);
		b.bound(midNode0, nodeOrNil);
		b.bound(farNode0, nodeOrNil);
		b.bound(nearNode1, nodeOrNil);
		b.bound(midNode1, nodeOrNil);
		b.bound(farNode1, nodeOrNil);	
		
		b.bound(next0, b.upperBound(next));
		b.bound(next1, b.upperBound(next));
		
		b.boundExactly(next, copyFrom(t, cex.tuples(repairer.next)));
		b.boundExactly(head, copyFrom(t, cex.tuples(repairer.head)));
		b.boundExactly(data, copyFrom(t, cex.tuples(repairer.data)));
		b.boundExactly(thisList, copyFrom(t, cex.tuples(repairer.thisList)));
		b.boundExactly(next3, copyFrom(t, cex.tuples(repairer.next3)));
		b.boundExactly(head0, copyFrom(t, cex.tuples(repairer.head0)));
		
		return b;
	}
	
	Solution debug(int size) {
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSatProver);
		solver.options().setCoreGranularity(1);
		solver.options().setLogTranslation(1);
		return solver.solve(debugSpec(), debugBounds(size));
	}
	
	Set<Formula> core(Solution sol) {
		final Set<Formula> core;
		if (sol.instance() == null) {
			final Proof proof = sol.proof();
			proof.minimize(new RCEStrategy(proof.log()));
			core = proof.highLevelCore().keySet();
		} else {
			core = Collections.emptySet();
		}
		return core;
	}
	
	void print(Set<Formula> core) { 
		System.out.println(PrettyPrinter.print(core, 3));
	}
	
	private void showDebug(int size) {
		final Solution sol = debug(size);
		System.out.println("************ DEBUG REVERSE FOR " + size + " NODES ************");
		System.out.println(sol.outcome());
		System.out.println();
		System.out.println(sol.stats());
		System.out.println();
		print(core(sol));
	}
	
	public static void main(String[] args) {
		ListDebug enc = new ListDebug();
		//enc.printEncoding();
		enc.showDebug(3);
	}

}
