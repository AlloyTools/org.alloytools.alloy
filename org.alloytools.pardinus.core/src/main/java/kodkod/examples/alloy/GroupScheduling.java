/* 
 * Kodkod -- Copyright (c) 2005-2007, Emina Torlak
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
package kodkod.examples.alloy;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Kodkod encoding of the group scheduling problem.
 * 
 * @author Emina Torlak
 *
 */
public final class GroupScheduling {
	private final Relation person, group, round, assign;
	private final int ng;
	
	public GroupScheduling(int numGroups) {
		assert numGroups > 0;
		this.person = Relation.unary("Person");
		this.group = Relation.unary("Group");
		this.round = Relation.unary("Round");
		this.assign = Relation.ternary("assign");
		this.ng = numGroups;
	}
	
	public Bounds bounds() {
		final int p = ng*ng, r = ng + 1;
		final List<String> a = new ArrayList<String>((ng+1)*(ng+1));
		for(int i = 0; i < p; i++) { 
			a.add("p"+i);
		}
		for(int i = 0; i < ng; i++) { 
			a.add("g"+i);
		}
		for(int i = 0; i < r; i++) { 
			a.add("r"+i);
		}
		final Universe u = new Universe(a);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		b.boundExactly(person, f.range(f.tuple("p0"), f.tuple("p" + (p-1))));
		b.boundExactly(group, f.range(f.tuple("g0"), f.tuple("g" + (ng-1))));
		b.boundExactly(round, f.range(f.tuple("r0"), f.tuple("r" + (r-1))));
		b.bound(assign, b.upperBound(person).product(b.upperBound(round)).product(b.upperBound(group)));
		final TupleSet low = f.noneOf(3);
		for(int i = 0; i < r; i++) {
			low.add(f.tuple("p0", "r"+i, "g0"));
			final int start = i*(ng-1) + 1, end = (i+1)*(ng-1);
			low.addAll(f.range(f.tuple("p"+start), f.tuple("p"+end)).product(f.setOf("r"+i)).product(f.setOf("g0")));
		}
		final TupleSet high = f.noneOf(3);
		high.addAll(low);
		high.addAll(f.range(f.tuple("p1"), f.tuple("p" + (p-1))).product(b.upperBound(round)).product(b.upperBound(group)));
		b.bound(assign, low, high);
		return b;
	}
	
	public Formula schedule() {
		final Variable p = Variable.unary("p"), r = Variable.unary("r"), g = Variable.unary("g");
		final Formula f0 = r.join(p.join(assign)).one().forAll(p.oneOf(person).and(r.oneOf(round)));
		final Formula f1 = assign.join(g).join(r).count().eq(IntConstant.constant(ng)).forAll(r.oneOf(round).and(g.oneOf(group)));
		final Variable pp = Variable.unary("p'");
		final Formula f2 = p.join(assign).intersection(pp.join(assign)).some().forAll(p.oneOf(person).and(pp.oneOf(person.difference(p))));
		return Formula.and(f0, f1, f2);
	}
	
	public static void main(String[] args) {
		final int ng = Integer.parseInt(args[0]);
		final GroupScheduling model = new GroupScheduling(ng);
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.plingeling());
		solver.options().setReporter(new ConsoleReporter());
		solver.options().setSymmetryBreaking(ng*ng*ng*ng);
		final Formula f = model.schedule();
		final Bounds b = model.bounds();
		
		final Solution sol = solver.solve(f, b);
		final Map<String, List<Tuple>> m = new LinkedHashMap<String, List<Tuple>>();
		final int p = ng*ng;
		for(Tuple t : sol.instance().tuples(model.assign)) {
			List<Tuple> l = m.get(t.atom(1));
			if (l==null) {  
				l = new ArrayList<Tuple>(p);
				m.put((String) t.atom(1), l);
			}
			l.add(t);
		}
		System.out.println(sol);
		for(Map.Entry<?, List<Tuple>> e : m.entrySet()) {
			System.out.println("ROUND " + e.getKey());
			for(Tuple t : e.getValue()) {
				System.out.println(" " + t.atom(0) + " -> "  + t.atom(2));
			}
		}
	}
}
