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

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Reads a graph from a file, formatted using the DIMACS or the ASP (http://asparagus.cs.uni-potsdam.de/?action=instances&id=30) graph format,
 * and finds a Hamiltonian cycle in it if one exists.
 * 
 * @author Emina Torlak
 */
public final class HamiltonianCycle {

	private final Relation vertex, start, edges, cycle;
	
	/**
	 * Constructs an instance of the encoding.
	 */
	public HamiltonianCycle() {
		this.vertex = Relation.unary("Vertex");
		this.start = Relation.unary("start");
		this.edges = Relation.binary("edges");
		this.cycle = Relation.binary("cycle");
	}
	
	/**
	 * Returns a formula that defines a Hamiltonian cycle.
	 * @return a formula that defines a Hamiltonian cycle
	 */
	public Formula cycleDefinition() {
		final Formula f0 = cycle.function(edges.join(vertex), vertex.join(edges));
		final Formula f1 = vertex.in(start.join(cycle.closure()));	
		return f0.and(f1);
	}

	/**
	 * Returns Bounds extracted from the graph 
	 * definition in the given file.
	 * @requires file is in the specified format  
	 * @return Bounds extracted from the graph 
	 * definition in the given file.
	 */
	public Bounds bounds(String file, Graph.Format format) {
		
		final Graph<?> graph = format.parse(file);
		final Universe u = new Universe(graph.nodes());
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		b.boundExactly(vertex, f.allOf(1));
		b.boundExactly(start, f.setOf(graph.start()==null ? u.atom(0) : graph.start()));
		final TupleSet edgeBound = f.noneOf(2);
		
		for(Object from : graph.nodes()) {
			for (Object to : graph.edges(from))
				edgeBound.add(f.tuple(from, to));
		}
		
		b.boundExactly(edges, edgeBound);
		b.bound(cycle, edgeBound);
		
		return b;
			
		
	}
	
	private static void usage() {
		System.out.println("Usage: examples.classicnp.HamiltonianCycle <graph file> <file format>");
		System.exit(1);
	}
	
	private final boolean verify(Instance instance) {
		
		final Evaluator eval = new Evaluator(instance);
		System.out.println(eval.evaluate(cycle));
		return eval.evaluate(cycleDefinition());
	}
	
	/**
	 * Usage: examples.classicnp.HamiltonianCycle <graph file> <DIMACS | ASP>
	 */
	public static void main(String[] args) {
		if (args.length!=2)
			usage();
		final HamiltonianCycle model = new HamiltonianCycle();
		final Formula f = model.cycleDefinition();
		final Bounds b = model.bounds(args[0], Enum.valueOf(Graph.Format.class, args[1].toUpperCase()));
		System.out.println(f);
		System.out.println(b);
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		solver.options().setReporter(new ConsoleReporter());
//		solver.options().setFlatten(false);
		final Solution s = solver.solve(f,b);
		System.out.println(s);
		if (s.instance()!=null) {
			System.out.print("verifying solution ... ");
			System.out.println(model.verify(s.instance()) ? "correct." : "incorrect!");
		}
	}
	
}
