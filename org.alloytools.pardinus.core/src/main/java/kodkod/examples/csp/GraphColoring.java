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
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;


/**
 * A decision version of the graph coloring problem.  Given a graph G and a number of colors k,
 * this class determines if G is k-colorable.  
 * See <a href="http://www.cs.hbg.psu.edu/txn131/graphcoloring.html">Graph Coloring Benchmark Instances</a> 
 * for example graph coloring problems instances.
 * @author Emina Torlak
 */
public final class GraphColoring {
	private final Relation vertex, color, edges, v2c;
	private final Bounds bounds;
	/**
	 * Constructs an instance of the graph coloring problem for the given graph and the number of colors.
	 * @requires colors > 0
	 */
	public GraphColoring(String file, Graph.Format format, int colors) {
		assert colors > 0;
		vertex = Relation.unary("Vertex");
		color = Relation.unary("Color");
		edges = Relation.binary("edges");
		v2c = Relation.binary("color");
		final Graph<?> g = format.parse(file);
		final int vertices = g.nodes().size();
		final List<Object> atoms = new ArrayList<Object>(vertices+colors);
		atoms.addAll(g.nodes());
		for(int i = 0 ; i < colors; i++) { atoms.add(new Color(i)); }
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		bounds = new Bounds(u);
		bounds.boundExactly(vertex, f.range(f.tuple(atoms.get(0)), f.tuple(atoms.get(vertices-1))));
		bounds.boundExactly(color, f.range(f.tuple(atoms.get(vertices)), f.tuple(atoms.get(atoms.size()-1))));
		bounds.bound(v2c, bounds.upperBound(vertex).product(bounds.upperBound(color)));
		final TupleSet edgeBound = f.noneOf(2);
		for(Object from : g.nodes()) {
			for (Object to : g.edges(from)) 
				edgeBound.add(f.tuple(from, to));
		}
//		for(Object from : g.nodes()) {
//			System.out.println(from + ": " + g.edges(from).size());
//		}
		bounds.boundExactly(edges, edgeBound);
		System.out.println("vertices: " + vertices + ", edges: " + edgeBound.size());
	}
	
	private static final class Color {
		final int value;
		Color(int value) { this.value = value; }
		public String toString() { return "color"+value; }
	}
	
	/**
	 * Returns a formula stating that all vertices
	 * have  one color, and that no two adjacent
	 * vertices have intersecting colors.
	 * @return a formula stating that all vertices
	 * have one color, and that no two adjacent
	 * vertices have intersecting colors.
	 */
	public Formula coloring() {
		final Variable v = Variable.unary("v");
		final Expression vcolor = v.join(v2c);
		final Formula f0 = vcolor.one();
		final Formula f1 = vcolor.intersection(v.join(edges).join(v2c)).no();
		return f0.and(f1).forAll(v.oneOf(vertex));
	}
	
	/**
	 * Returns the bounds for this coloring problem.
	 * @return bounds for this coloring problem
	 */
	public Bounds bounds() { 
		return bounds.unmodifiableView();
	}
	
	private static void usage() { 
		System.out.println("Usage: java examples.classicnp.GraphColoring <filename> <DIMACS | ASP | ASP_EDGES> <# of colors>");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.classicnp.GraphColoring <filename> <DIMACS | ASP | ASP_EDGES> <# of colors>
	 */
	public static void main(String[] args) {
		if (args.length!=3) usage();
		
		try {
			final GraphColoring model = new GraphColoring(args[0], Enum.valueOf(Graph.Format.class, args[1].toUpperCase()), Integer.parseInt(args[2]));
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setSymmetryBreaking(0);
			solver.options().setReporter(new ConsoleReporter());
			final Formula f = model.coloring();
			final Bounds b = model.bounds();
			final Solution sol = solver.solve(f, b);
			System.out.println(sol.outcome());
			System.out.println(sol.stats());
			//if (sol.instance()!=null)
			//	System.out.println("coloring: "+sol.instance().tuples(model.v2c));

		} catch (NumberFormatException e) { usage(); }
	}
}
