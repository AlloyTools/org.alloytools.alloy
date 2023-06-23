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

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.Multiplicity;
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
 * Reads a graph from a file, formatted using the DIMACS or the ASP (http://asparagus.cs.uni-potsdam.de/?action=instances&id=30) graph format,
 * and finds a Hamiltonian cycle in it if one exists.  This encoding is more efficient than, but not as nice as, {@linkplain HamiltonianCycle}.
 * 
 * @author Emina Torlak
 */
public final class HamiltonianCycle2 {
	private final Expression[] pts;
	private final Relation edges, vertex;
	private final Bounds bounds;
	private final Multiplicity ptMult;
	
	private HamiltonianCycle2(Bounds bounds, Expression[] pts, Multiplicity ptMult, Relation vertex, Relation edges) { 
		this.pts = pts;
		this.ptMult = ptMult;
		this.vertex = vertex;
		this.edges = edges;
		this.bounds = bounds;
	}
	
	/**
	 * Returns a log encoded instance of HamiltonianCycle2.
	 * @return  a log encoded instance of HamiltonianCycle2.
	 */
	public static HamiltonianCycle2 logEncoding(String file, Graph.Format format ) {
		final Graph<?> graph = format.parse(file);
		final Relation edges = Relation.binary("edges");
		final Relation enc = Relation.binary("enc");
		final Relation vertex = Relation.unary("vertex");
		final Relation[] pts = new Relation[graph.nodes().size()];
		for(int i = 0; i < pts.length; i++) { pts[i] = Relation.unary("p"+i); }
		
		final int bits =  33 - Integer.numberOfLeadingZeros(pts.length-1);
		final List<Object> atoms = new ArrayList<Object>(pts.length + bits);
		atoms.addAll(graph.nodes());
		for(int i = 0; i < bits; i++) { atoms.add(new Bit(i)); }
		
		final Bounds bounds = new Bounds(new Universe(atoms));
		
		final TupleFactory f = bounds.universe().factory();
		final TupleSet edgeBound = f.noneOf(2);
		for(Object from : graph.nodes()) {
			for (Object to : graph.edges(from))
				edgeBound.add(f.tuple(from, to));
		}
		
		bounds.boundExactly(edges, edgeBound);
		
		bounds.boundExactly(pts[0], f.setOf(atoms.get(pts.length)));
		for(int i = 1; i < pts.length; i++) { 
			bounds.bound(pts[i], f.range(f.tuple(atoms.get(pts.length)), f.tuple(atoms.get(atoms.size()-1))));
		}
		bounds.boundExactly(vertex, f.range(f.tuple(atoms.get(0)), f.tuple(atoms.get(pts.length-1))));
		
		final TupleSet encBound = f.noneOf(2);
		for(int i = 1; i <= pts.length; i++) { 
			final Object iatom = atoms.get(i-1);
			for(int j = 0; j < bits; j++) { 
				if ((i & (1<<j)) != 0) { 
					encBound.add(f.tuple(iatom, atoms.get(pts.length+j)));
				}
			}
		}
		bounds.boundExactly(enc, encBound);
		
		final Expression[] exprs = new Expression[pts.length];
		final Variable v = Variable.unary("v");
		final Decls d = v.oneOf(vertex);
		for(int i = 0; i < exprs.length; i++) { 
			exprs[i] = pts[i].eq(v.join(enc)).comprehension(d);
		}
		
		return new HamiltonianCycle2(bounds, exprs, Multiplicity.SOME, vertex, edges);
	}
	

	/**
	 * Returns an ext encoded instance of HamiltonianCycle2.
	 * @return  an ext encoded instance of HamiltonianCycle2.
	 */
	public static HamiltonianCycle2 extEncoding(String file, Graph.Format format ) {
		final Graph<?> graph = format.parse(file);
		final Relation edges = Relation.binary("edges");
		final Relation vertex = Relation.unary("vertex");
		final Relation[] pts = new Relation[graph.nodes().size()];
		for(int i = 0; i < pts.length; i++) { pts[i] = Relation.unary("p"+i); }

		final Universe univ = new Universe(graph.nodes());
		final Bounds bounds = new Bounds(univ);
		final TupleFactory f = univ.factory();
		
		final TupleSet edgeBound = f.noneOf(2);
		for(Object from : graph.nodes()) {
			for (Object to : graph.edges(from))
				edgeBound.add(f.tuple(from, to));
		}
		
		bounds.boundExactly(edges, edgeBound);
		
		bounds.boundExactly(pts[0], f.setOf(graph.start()==null ? univ.atom(0) : graph.start()));
		for(int i = 1; i < pts.length; i++) { 
			bounds.bound(pts[i], f.range(f.tuple(univ.atom(1)), f.tuple(univ.atom(univ.size()-1))));
		}
		bounds.boundExactly(vertex, f.allOf(1));
		
		return new HamiltonianCycle2(bounds, pts, Multiplicity.ONE, vertex, edges);
	}
	
	private static final class Bit {
		final int value;
		Bit(int bit) { this.value = 1<<bit; }
		public String toString() { return value+"";	}
	}
	
	/**
	 * Returns a formula that defines a Hamiltonian cycle.
	 * @return a formula that defines a Hamiltonian cycle
	 */
	public final Formula cycleDefinition() {
		final List<Formula> formulas = new ArrayList<Formula>();
		for(Expression e : pts) { 
			formulas.add( e.apply(ptMult) );
		}
		for(int i = 1; i < pts.length; i++) { 
			formulas.add( pts[i-1].product(pts[i]).in(edges) );
		}
		formulas.add( pts[pts.length-1].product(pts[0]).in(edges) ); 
		formulas.add(Expression.union(pts).eq(vertex));
		return Formula.and(formulas);
	}

	
	/**
	 * Returns the Bounds for the given cycle instance.
	 * @return Bounds for the given cycle instance.
	 */
	public final Bounds bounds( ) {
		return bounds.unmodifiableView();
	}
	
	private static void usage() {
		System.out.println("Usage: examples.classicnp.HamiltonianCycle2 <graph file> <DIMACS | ASP> <EXT | LOG>");
		System.exit(1);
	}
	
	/**
	 * Usage: examples.classicnp.HamiltonianCycle2 <graph file> <DIMACS | ASP> <EXT | LOG>
	 */
	public static void main(String[] args) {
		if (args.length!=3)
			usage();
		final HamiltonianCycle2 model;
		if ("LOG".equals(args[2].toUpperCase())) {
		  model = logEncoding(args[0], Enum.valueOf(Graph.Format.class, args[1].toUpperCase()));
		} else if ("EXT".equals(args[2].toUpperCase())) {
		  model = extEncoding(args[0], Enum.valueOf(Graph.Format.class, args[1].toUpperCase()));
		} else {
			usage();
			model = null;
		}
		final Formula f = model.cycleDefinition();
		final Bounds b = model.bounds();
		System.out.println(f);
		System.out.println(b);
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		solver.options().setReporter(new ConsoleReporter());
//		solver.options().setFlatten(false);
		final Solution s = solver.solve(f,b);
		System.out.println(s.outcome());
		System.out.println(s.stats());
		if (s.instance()!=null) {
			final Evaluator eval = new Evaluator(s.instance(), solver.options());
			final Expression[] dec = model.pts;
			System.out.print(eval.evaluate(dec[0]));
			for(int i = 1; i < dec.length; i++) { 
				System.out.print(" -> " + eval.evaluate(dec[i]));
			}
			System.out.println();
		}
	}
}
