package kodkod.examples.csp;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;


public class GraphColoring2  {
	private final Relation[] vcolors;
	private final int[][] graph;
	private final Bounds bounds;
	/**
	 * Constructs an instance of the graph coloring problem for the given graph and the number of colors.
	 * @requires colors > 0
	 */
	public GraphColoring2(String file, Graph.Format format, int colors) {
		assert colors > 0;
		final Graph<?> g =   format.parse(file);
		final int vertices = g.nodes().size();
		vcolors = new Relation[vertices];   
		for(int i = 0; i < vertices; i++) { 
			vcolors[i] = Relation.unary("v"+i+"color");
		}
		final List<Object> atoms = new ArrayList<Object>(colors);
		for(int i = 0 ; i < colors; i++) { atoms.add(new Color(i)); }
		final Universe u = new Universe(atoms);
		bounds = new Bounds(u);
		final TupleSet all = u.factory().allOf(1);
		for(Relation r : vcolors) { 
			bounds.bound(r, all);
		}
		graph = new int[vertices][];
		final Map<Object,Integer> ids = new LinkedHashMap<Object, Integer>();
		int i = 0;
		for(Object n : g.nodes()) { 
			ids.put(n, i++);
		}
		i = 0;
		for(Object n : g.nodes()) { 
			final Set<?> neighbors = g.edges(n);
			graph[i] = new int[neighbors.size()];
			int j = 0;
			for(Object neighbor : neighbors) { 
				graph[i][j++] = ids.get(neighbor);
			}
			i++;
		}
		
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
		final List<Formula> formulas = new ArrayList<Formula>(vcolors.length);
		for(Relation r : vcolors) { 
			formulas.add( r.one() );
		}
		for(int i = 0; i < vcolors.length; i++) { 
			final int[] neighbors = graph[i];
			final int max = neighbors.length;
			final Relation vcolor = vcolors[i];
			for(int j = 0; j < max; j++) { 
				formulas.add( vcolor.intersection(vcolors[neighbors[j]]).no() );
			}
		}
		return Formula.and(formulas);
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
			final GraphColoring2 model = new GraphColoring2(args[0], Enum.valueOf(Graph.Format.class, args[1].toUpperCase()), Integer.parseInt(args[2]));
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

