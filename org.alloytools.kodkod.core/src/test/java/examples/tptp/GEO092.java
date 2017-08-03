/**
 * 
 */
package examples.tptp;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

/**
 * The  GEO092+1 problem from http://www.cs.miami.edu/~tptp/
 * 
 * @author Emina Torlak
 */
public class GEO092 extends GEO158 {

	/**
	 * Constructs a new instance of GEO091.
	 */
	public GEO092() {
		super();
		// TODO Auto-generated constructor stub
	}
	
	/*
	 * fof(proposition_2_14_1,conjecture,
    ( ! [C1,C2,P] : 
        ( ( meet(P,C1,C2)
          & open(sum(C1,C2)) )
       => ! [Q] : 
            ( Q != P
           => ~ ( incident_c(Q,C1)
                & incident_c(Q,C2) ) ) ) )).
	 */
	/**
	 * Returns the conjecture proposition_2_14_1.
	 * @return proposition_2_14_1
	 */
	public final Formula proposition2141() {	
		// all c1, c2: curve, p: point | 
		//  p->c1->c2 in meet && c1->c2 in sum.open => 
		//  all q: point - p | c1 + c2 !in q.incident
		final Variable c1 = Variable.unary("C1");
		final Variable c2 = Variable.unary("C2");
		final Variable p = Variable.unary("P");
		final Variable q = Variable.unary("Q");
		final Expression e0 = c1.product(c2);
		final Formula f0 = p.product(e0).in(meet).and(e0.in(sum.join(open)));
		final Formula f1 = c1.union(c2).in(q.join(incident)).not().forAll(q.oneOf(point.difference(p)));
		return f0.implies(f1).forAll(c1.oneOf(curve).and(c2.oneOf(curve)).and(p.oneOf(point)));
	}

	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !proposition2141()
	 */
	public final Formula checkProposition2141() { 
		return axioms().and(proposition2141().not());
	}
	
	
	private static void usage() {
		System.out.println("java examples.tptp.GEO192 [scope]");
		System.exit(1);
	}
	
	/**
	 * Usage: ava examples.tptp.GEO192 [# curves] [# points]
	 */
	public static void main(String[] args) {
		if (args.length < 2)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
		
	
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			final GEO092 model = new GEO092();
			final Formula f = model.checkProposition2141();
			
			System.out.println(model.proposition2141());
			
			final Bounds b = model.bounds(n);
			final Solution sol = solver.solve(f,b);
			
			System.out.println(sol);
			//System.out.println((new Evaluator(sol.instance())).evaluate(model.axioms().and(model.theorem213().not())));
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
