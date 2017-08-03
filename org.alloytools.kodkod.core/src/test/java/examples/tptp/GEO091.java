package examples.tptp;

import kodkod.ast.Formula;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

/**
 * The  GEO091+1 problem from http://www.cs.miami.edu/~tptp/
 * 
 * @author Emina Torlak
 */
public class GEO091 extends GEO158 {

	/**
	 * Constructs a new instance of GEO091.
	 */
	public GEO091() {
		super();
		// TODO Auto-generated constructor stub
	}
	
	/**
	 * Returns the conjecture theorem_2_13.
	 * @return theorem_2_13
	 */
	public final Formula theorem_2_13() {
		//  all C, C1, C2: Curve | 
		//   ((C1 + C2)->C in partOf && C in Open &&
		//   !(lone endPoint.C1 & endPoint.C2)) => C1 = C2
		final Variable c = Variable.unary("C");
		final Variable c1 = Variable.unary("C1");
		final Variable c2 = Variable.unary("C2");
		final Formula f0 = c1.union(c2).product(c).in(partOf).and(c.in(open));
		final Formula f1 = endPoint.join(c1).intersection(endPoint.join(c2)).lone().not();
		return f0.and(f1).implies(c1.eq(c2)).forAll(c.oneOf(curve).and(c1.oneOf(curve)).and(c2.oneOf(curve)));
	}

	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !theorem_2_13()
	 */
	public final Formula checkTheorem_2_13() { 
		return axioms().and(theorem_2_13().not());
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.GEO191 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.GEO191 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
	
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			final GEO091 model = new GEO091();
			final Formula f = model.checkTheorem_2_13();
			
			System.out.println(model.theorem_2_13());
			
			final Bounds b = model.bounds(n);
			final Solution sol = solver.solve(f,b);
			
			System.out.println(sol);
			//System.out.println((new Evaluator(sol.instance())).evaluate(model.axioms().and(model.theorem213().not())));
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
