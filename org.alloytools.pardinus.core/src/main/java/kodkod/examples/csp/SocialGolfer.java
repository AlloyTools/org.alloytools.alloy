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

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * A Kodkod encoding of the social golfer problem.
 * @author Emina Torlak
 */
public final class SocialGolfer {
	private final Relation plays, player, week, group, size;
	
	/**
	 * Constructs a new instance of the social golfer problem.
	 */
	public SocialGolfer() {
		plays = Relation.ternary("plays");
		player = Relation.unary("player");
		week = Relation.unary("week");
		group = Relation.unary("group");
		size = Relation.unary("size");
	}

	/**
	 * Returns the constraints on the playing schedule.
	 * @return constraints on the playing schedule.
	 */
	public final Formula schedule() {
		final Variable p = Variable.unary("p"), w = Variable.unary("w"), g = Variable.unary("g");
		final Formula f0 = w.join(plays).join(p).one().forAll(p.oneOf(player).and(w.oneOf(week)));
		final IntExpression groupsize = size.sum();
		final Formula f1 = g.join(w.join(plays)).count().eq(groupsize).forAll(g.oneOf(group).and(w.oneOf(week)));
		final Variable p1 = Variable.unary("p1"), p2 = Variable.unary("p2");
		final Formula f2 = plays.join(p1).intersection(plays.join(p2)).lone().forAll(p1.oneOf(player).and(p2.oneOf(player.difference(p1))));
		return Formula.and(f0,f1,f2);
	}

	/**
	 * Returns the bounds for the scheduling problem with the given number of players, groups and weeks, using
	 * the specified group size.
	 * @return bounds for the scheduling problem with the given number of players, groups and weeks, using
	 * the specified group size.
	 */
	public final Bounds bounds(int players, int groups, int weeks, int size) { 
		if (players<1 || groups<1 || weeks<1 || size<1) throw new IllegalArgumentException("invalid schedule parameters");
		final List<Object> atoms = new ArrayList<Object>(players+groups+weeks+1);
		for(int i = 0; i < players; i++) { 
			atoms.add("p" + i);
		}
		for(int i = 0; i < groups; i++) { 
			atoms.add("g" + i);
		}
		for(int i = 0; i < weeks; i++) { 
			atoms.add("w" + i);
		}
		atoms.add(size);
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		b.boundExactly(size, f.setOf(size));
		b.boundExactly(this.size, f.setOf(size));
		b.boundExactly(this.player, f.range(f.tuple("p0"), f.tuple("p"+(players-1))));
		b.boundExactly(this.group, f.range(f.tuple("g0"), f.tuple("g"+(groups-1))));
		b.boundExactly(this.week, f.range(f.tuple("w0"), f.tuple("w"+(weeks-1))));
		b.bound(this.plays, b.upperBound(week).product(b.upperBound(group)).product(b.upperBound(player)));
		return b;
	}
	
	private static void usage() { 
		System.out.println("Usage: java examples.classicnp.SocialGolfer <players> <groups> <weeks> <group size>");
		System.exit(1);
	}
	
	private void print(Solution sol, Solver s) { 
		if (sol.instance()==null)
			System.out.println(sol);
		else {
			System.out.println(sol.outcome());
			System.out.println(sol.stats());
			System.out.println("Schedule:");
			for(Tuple t : sol.instance().tuples(plays)) { 
				System.out.print(t.atom(0)+"->"+t.atom(1)+"->"+t.atom(2) + "; ");
			}
			System.out.println();
		}
	}
	
	/**
	 * Usage: java examples.classicnp.SocialGolfer <players> <groups> <weeks> <group size>
	 */
	public static void main(String[] args) { 
		if (args.length<4) usage();
		try {
			final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
			bean.setThreadCpuTimeEnabled(true);
			final long start = bean.getCurrentThreadUserTime();
			final int players = Integer.parseInt(args[0]);
			final int groups = Integer.parseInt(args[1]);
			final int weeks = Integer.parseInt(args[2]);
			final int size = Integer.parseInt(args[3]);
			if (players<1 || groups<1 || weeks<1 || size<1) usage();
			final SocialGolfer model = new SocialGolfer();
			final Formula f = model.schedule();
			final Bounds b = model.bounds(players, groups, weeks, size);
//			System.out.println(PrettyPrinter.print(f, 2));
//			System.out.println(b);
			final Solver s = new Solver();
			s.options().setSolver(SATFactory.MiniSat);
			s.options().setBitwidth(32-Integer.numberOfLeadingZeros(groups*weeks));
//			s.options().setReporter(new ConsoleReporter());
			s.options().setSymmetryBreaking(1000);
			final Solution sol = s.solve(f, b);
			model.print(sol,s);
			final long end = bean.getCurrentThreadUserTime();
			System.out.println("Total time: " + (end-start)/1000000);
		} catch (NumberFormatException nfe) { 
			usage();
		}
	}
}
