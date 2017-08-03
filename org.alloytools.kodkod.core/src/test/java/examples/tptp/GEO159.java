/**
 * 
 */
package examples.tptp;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;

/**
 * The  GEO159+1 problem from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public class GEO159 extends GEO158 {
	final Relation between;
	/*
	 * beteween	:	C -> P -> P -> P
	 */
	/**
	 * Constructs a new instance of GEO159.
	 */
	public GEO159() {
		between = Relation.nary("between_c", 4);
	}
	
	/**
	 * Returns the between_c_defn axiom.
	 * @return between_c_defn
	 */
	public final Formula betweenDefn() {
		// all c, p, q, r: point | 
		//  c->p->q->r in between <=> p != r && some p.endPoint & r.endPoint & q.innerPoint & partOf.c
		final Variable c = Variable.unary("C");
		final Variable p = Variable.unary("P");
		final Variable q = Variable.unary("Q");
		final Variable r = Variable.unary("R");
		final Expression e = p.join(endPoint).intersection(r.join(endPoint)).
			intersection(q.join(innerPoint)).intersection(partOf.join(c));
		final Formula f0 = c.product(p).product(q).product(r).in(between);
		final Formula f1 = p.eq(q).not().and(e.some());
		return f0.iff(f1).forAll(p.oneOf(point).and(q.oneOf(point)).and(r.oneOf(point)).and(c.oneOf(curve)));
	}
	
	/**
	 * Returns all the 'type' declarations.
	 * @return the type declarations
	 */
	public Formula decls() {
		return super.decls().and(between.in(curve.product(point).product(point).product(point)));
	}
	
	/**
	 * Returns the conjunction of all axioms and decls
	 * @returns the conjunction of all axioms and decls
	 */
	public Formula checkDefs() {
		return super.axioms().and(betweenDefn()).and(someCurve());
	}
	
	
	/**
	 * Returns a bounds with the given number of maximum curves and points
	 * @return a bounds with the given number of maximum curves and points
	 */
	public Bounds bounds(int scope) {
		final Bounds b = super.bounds(scope);
		final TupleSet c = b.upperBound(curve);
		final TupleSet p = b.upperBound(point);
		b.bound(between, c.product(p).product(p).product(p));
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.GEO159 [scope]");
		System.exit(1);
	}
	
	/**
	 * Usage: ava examples.tptp.GEO159 [scope]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);

			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
	
			final GEO159 model = new GEO159();
			final Formula f = model.checkDefs();
			
			final Bounds b = model.bounds(n);
			final Solution sol = solver.solve(f,b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
