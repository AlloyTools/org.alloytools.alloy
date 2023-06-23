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
package kodkod.examples.csp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A Kodkod encoding of the magic series problem.
 * @author Emina Torlak
 */
public final class MagicSeries {
	private final Relation num, bits, el;
	
	/**
	 * Constructs an instance of the magic series problem.
	 */
	public MagicSeries() { 
		num = Relation.unary("num");
		bits = Relation.binary("bits");
		el = Relation.binary("el");
	}
	
	/**
	 * Returns the magic series formula.
	 * @return the magic series formula.
	 */
	public final Formula magic() {
		final Variable x = Variable.unary("x"), y = Variable.unary("y");
//		final Expression e = y.join(el).eq(x).comprehension(y.oneOf(num));
//		final Formula f1 = x.join(el).one().and(x.join(el).sum().eq(e.count())).forAll(x.oneOf(num));
		final Expression e = y.join(el).eq(x.join(bits)).comprehension(y.oneOf(num));
		final Formula f1 = x.join(el).sum().eq(e.count()).forAll(x.oneOf(num));
		return f1;
	}
	
	/**
	 * Bounds for a series with the given maximum.
	 * @return bounds for a series with the given maximum.
	 */
	public final Bounds bounds(int max) { 
		if (max<1) throw new IllegalArgumentException("max must be 1 or greater: " + max);
		final List<Integer> atoms = new ArrayList<Integer>(max);
		for(int i = 0; i <= max; i++) { 
			atoms.add(i);
		}
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		b.boundExactly(num, f.allOf(1));
		final int numBits = 32-Integer.numberOfLeadingZeros(max);
		final TupleSet bitAtoms = f.noneOf(1);
		for(int i = 0; i < numBits; i++) { 
			bitAtoms.add(f.tuple(1<<i));
			b.boundExactly(1<<i, f.setOf(1<<i));
		}
		b.bound(el, f.allOf(1).product(bitAtoms));
		final TupleSet num2bits = f.noneOf(2);
		for(int i = 0; i <= max; i++) { 
			for(int j = 0; j < numBits; j++) { 
				final int bit = 1<<j;
				if ((i&bit)!=0) num2bits.add(f.tuple((Object)i, bit));
			}
		}
		b.boundExactly(bits, num2bits);
//		b.bound(el, f.allOf(2));
//		for(int i = 0; i<=max; i++) { 
//			b.boundExactly(i, f.setOf(i));
//		}
		return b;
	}
	
	private static void usage() { 
		System.out.println("java examples.classicnp.MagicSeries <maximum number in the series>");
		System.exit(1);
	}
	
	private void print(Solution sol, Solver s) { 
		if (sol.instance()==null)
			System.out.println(sol);
		else {
			System.out.println(sol.outcome());
			System.out.println(sol.stats());
			final Evaluator eval = new Evaluator(sol.instance(), s.options());
			final Relation r = Relation.unary("r");
			final TupleFactory f = sol.instance().universe().factory();
			for(Object atom : f.universe()) { 
				eval.instance().add(r,  f.setOf(atom));
				System.out.print(atom + "->" + eval.evaluate(r.join(el).sum()) + "; ");
			}
			System.out.println();
		}
	}
	
	/**
	 * Usage: java examples.classicnp.MagicSeries <maximum number in the series>
	 */
	public static void main(String[] args) { 
		if (args.length<1) usage();
		try {
			final int max = Integer.parseInt(args[0]);
			if (max < 1) usage();
			final MagicSeries model = new MagicSeries();
			final Formula f = model.magic();
			final Bounds b = model.bounds(max);
//			System.out.println(f);
//			System.out.println(b);
			final Solver s = new Solver();
			s.options().setSolver(SATFactory.MiniSat);
			s.options().setBitwidth(33-Integer.numberOfLeadingZeros(max));
			s.options().setReporter(new ConsoleReporter());
			final Solution sol = s.solve(f, b);
			model.print(sol,s);
			
		} catch (NumberFormatException nfe) { 
			usage();
		}
	}
}
