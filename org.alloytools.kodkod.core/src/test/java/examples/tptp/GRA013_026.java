/**
 * 
 */
package examples.tptp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.nodes.PrettyPrinter;

/**
 * A KK encoding of GRA019+1.p through GRA026+1.p from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public final class GRA013_026 {
	private final Relation red, green, lessThan,goal,node;
	private final int graphSize, cliqueSize;
	
	/**
	 * Constructs a new instance of GRA013_026 with the given graph and clique size.
	 * @requires 0 < cliqueSize <= graphSize
	 */
	public GRA013_026(int graphSize, int cliqueSize) {
		if (cliqueSize <= 0) throw new IllegalArgumentException("cliqueSize must be positive: " + cliqueSize);
		if (cliqueSize > graphSize) throw new IllegalArgumentException("cliqueSize must be less than or equal to graph size: " + cliqueSize + ">" + graphSize);
		node = Relation.unary("N");
		red = Relation.binary("red");
		green = Relation.binary("green");
		lessThan = Relation.binary("lessThan");
		goal = Relation.unary("goal");
		this.graphSize = graphSize;
		this.cliqueSize = cliqueSize;
	}
	
	private final Formula cliqueAxiom(Expression color) {
		final Variable[] vars = new Variable[cliqueSize];
		for(int i = 0; i < cliqueSize; i++) { 
			vars[i] = Variable.unary("V"+i);
		}
		final List<Expression> members = new ArrayList<Expression>(cliqueSize);
		for(int i = 0, max = cliqueSize-1; i < max; i++) { 
			final List<Expression> tmp = new ArrayList<Expression>();
			for(int j = i+1; j < cliqueSize; j++) { 
				tmp.add(vars[j]);
			}
			members.add(vars[i].product(Expression.union(tmp)));
		}
		Decls d = vars[0].oneOf(node);
		for(int i = 1; i < cliqueSize; i++) { 
			d = d.and(vars[i].oneOf(vars[i-1].join(lessThan)));
		}
		return Expression.union(members).in(color).implies(goalToBeProved()).forAll(d);
	}
	
	
	/**
	 * Returns the red clique axiom.
	 * @return red clique axiom.
	 */
	public final Formula redCliqueAxiom() {
		return cliqueAxiom(red);
	}
	
	/**
	 * Returns the green clique axiom.
	 * @return green clique axiom.
	 */
	public final Formula greenCliqueAxiom() {
		return cliqueAxiom(green);
	}
	
	/**
	 * Returns the partition axiom.
	 * @return partition axiom
	 */
	public final Formula partition() {
		return lessThan.in(red.union(green));
	}
	
	/**
	 * Returns the transitivity axiom.
	 * @return transitivity axiom
	 */
	public final Formula lessThanTransitive() { 
		return lessThan.join(lessThan).in(lessThan);
	}
	
	/**
	 * Returns the no overlap axiom.
	 * @return no overlap axiom.
	 */
	public final Formula noOverlap() { 
		return red.intersection(green).no();
	}
	
	/**
	 * Returns the conjunction of all axioms.
	 * @return conjunction of all axioms
	 */
	public final Formula axioms() {
		return Formula.and(redCliqueAxiom(), greenCliqueAxiom(), partition(), lessThanTransitive(), noOverlap());
	}
	
	/**
	 * Returns the goal_to_be_proved conjecture.
	 * @return goal_to_be_proved conjecture.
	 */
	public final Formula goalToBeProved() { 
		return goal.some();
	}
	
	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !goalToBeProved()
	 */
	public final Formula checkGoalToBeProved() { 
		return axioms().and(goalToBeProved().not());
	}
	
	/**
	 * Returns the bounds.
	 * @return the bounds
	 */
	public final Bounds bounds() {
		final List<String> atoms = new ArrayList<String>(graphSize);
		for(int i = 1; i <= graphSize; i++)
			atoms.add("n"+i);
		atoms.add("goal");
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		b.bound(goal, f.setOf("goal"));
		final TupleSet ns = f.range(f.tuple("n1"), f.tuple("n"+graphSize));
		b.boundExactly(node, ns);
		
		final TupleSet s = f.noneOf(2);
		for(int i = 1; i < graphSize; i++) {
			for(int j = i+1; j < graphSize; j++)
				s.add(f.tuple("n"+i, "n"+j));
		}
		b.boundExactly(lessThan, s);
		b.bound(red, s);
		b.bound(green, s);
		return b;
	}
	
	private static void usage() {
		System.out.println("Usage: java examples.tptp.GRA013_026 <graph size> <clique size>");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.GRA013_026 <graph size> <clique size>
	 */
	public  static void main(String[] args) {
		if (args.length < 2)
			usage();
		try {

			final GRA013_026 model = new GRA013_026(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
			
			final Bounds b = model.bounds();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setReporter(new ConsoleReporter());
			
			final Formula f = model.checkGoalToBeProved();
			System.out.println(PrettyPrinter.print(f, 2));
//			System.out.println(b);
			final Solution s = solver.solve(f, b);
			System.out.println(s);
			//System.out.println((new Evaluator(s.instance())).evaluate(f));
	
		} catch (HigherOrderDeclException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnboundLeafException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
