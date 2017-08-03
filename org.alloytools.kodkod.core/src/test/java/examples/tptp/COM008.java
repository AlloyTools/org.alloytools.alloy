/**
 * 
 */
package examples.tptp;

import static kodkod.ast.Expression.IDEN;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
/**
 * A KK encoding of COM008+1.p from http://www.cs.miami.edu/~tptp/
 * 
 * @author Emina Torlak
 */
public final class COM008 {
	private final Relation equalish, rewrite, trr;
	private final Relation a, b, c, goal;
	private final Relation Atom;
	
	/**
	 * Constructs a new instance of COM008.
	 */
	public COM008() {
		equalish = Relation.binary("equalish");
		rewrite = Relation.binary("rewrite");
		trr = Relation.binary("trr");
		a = Relation.unary("a");
		b = Relation.unary("b");
		c = Relation.unary("c");
		goal = Relation.unary("goal");
		Atom = Relation.unary("Atom");
	}
	
	/**
	 * Returns the declarations.
	 * @return one a && one b && one c
	 */
	public final Formula decls() { 
		return a.one().and(b.one()).and(c.one());
	}
	
	/**
	 * Returns the found axiom.
	 * @return the found axiom.
	 */
	public final Formula found() {
		final Variable A = Variable.unary("A");
		return b.product(A).union(c.product(A)).in(trr).implies(goal.some()).forAll(A.oneOf(Atom));
	}
	
	/**
	 * Returns the assumption axiom.
	 * @return the assumption axiom.
	 */
	public final Formula assumption() { 
		return a.product(b).union(a.product(c)).in(trr);
	}
	
	/**
	 * Returns the reflexivity axiom.
	 * @return the reflexivity axiom.
	 */
	public final Formula reflexivity() {
		final Expression eqdom = equalish.join(Atom);
		return eqdom.product(eqdom).intersection(IDEN).in(equalish);
	}
	
	/**
	 * Returns the symmetry axiom.
	 * @return the symmetry axiom.
	 */
	public final Formula symmetry() {
		return equalish.eq(equalish.transpose());
	}
	
	/**
	 * Returns the equalish_in_transitive_reflexive_rewrite axiom.
	 * @return the equalish_in_transitive_reflexive_rewrite axiom.
	 */
	public final Formula equalishInTrr() {
		return equalish.in(trr);
	}

	/**
	 * Returns the rewrite_in_transitive_reflexive_rewrite axiom.
	 * @return the rewrite_in_transitive_reflexive_rewrite axiom.
	 */
	public final Formula rewriteInTrr() {
		return rewrite.in(trr);
	}
	
	/**
	 * Returns the transitivity_of_transitive_reflexive_rewrite axiom.
	 * @return the transitivity_of_transitive_reflexive_rewrite axiom.
	 */
	public final Formula transitivityOfTrr() {
		return trr.join(trr).in(trr);
	}
	
	/**
	 * Returns the lo_cfl axiom.
	 * @return the lo_cfl axiom.
	 */
	public final Formula loCfl() {
		final Variable A = Variable.unary("A");
		final Variable B = Variable.unary("B");
		final Variable C = Variable.unary("C");
		final Formula f0 = A.product(B).union(A.product(C)).in(rewrite);
		final Formula f1 = B.join(trr).intersection(C.join(trr)).some();
		return f0.implies(f1).forAll(A.oneOf(Atom).and(B.oneOf(Atom)).and(C.oneOf(Atom)));
	}
	/**
	 * Returns the ih_cfl axiom.
	 * @return the ih_cfl axiom.
	 */
	public final Formula ihCfl() { 
		final Variable A = Variable.unary("A");
		final Variable B = Variable.unary("B");
		final Variable C = Variable.unary("C");
		final Formula f0 = a.product(A).in(rewrite).and(A.product(B).union(A.product(C)).in(trr));
		final Formula f1 = B.join(trr).intersection(C.join(trr)).some();
		return f0.implies(f1).forAll(A.oneOf(Atom).and(B.oneOf(Atom)).and(C.oneOf(Atom)));
	}
	/**
	 * Returns the equalish_or_rewrite axiom.
	 * @return the equalish_or_rewrite axiom.
	 */
	public final Formula equalishOrRewrite() {
		final Variable A = Variable.unary("A");
		final Variable B = Variable.unary("B");
		final Formula f0 = A.product(B).in(trr);
		final Formula f1 = A.product(B).in(equalish);
		final Formula f2 = A.join(rewrite).intersection(trr.join(B)).some();
		return f0.implies(f1.or(f2)).forAll(A.oneOf(Atom).and(B.oneOf(Atom)));
	}
	
	public final Formula axioms() { 
		return decls().and(equalishInTrr()).and(rewriteInTrr()).
			   and(found()).and(assumption()).and(reflexivity()).
		       and(symmetry()).
		       and(transitivityOfTrr()).and(loCfl()).and(ihCfl()).
		       and(equalishOrRewrite());
	}
	
	/**
	 * Returns the conjecture.
	 * @return some goal
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
	 * Returns bounds for the given scope.
	 * @return bounds for the given scope.
	 */
	public final Bounds bounds(int n) {
		assert n > 0;
		final List<String> atoms = new ArrayList<String>(n);
		atoms.add("goal");
		for(int i = 0; i < n; i++)
			atoms.add("a"+i);
		final Universe u = new Universe(atoms);
		final Bounds bound = new Bounds(u);
		final TupleFactory f = u.factory();
		final TupleSet d1 = f.range(f.tuple("a0"), f.tuple("a"+(n-1)));
		final TupleSet d2 = d1.product(d1);
		
		bound.bound(rewrite, d2);
		bound.bound(equalish, d2);
		
		
		bound.bound(a, d1);
		bound.bound(b, d1);
		bound.bound(c, d1);
		bound.boundExactly(Atom, d1);
		
		bound.bound(trr, d2);
		
		bound.bound(goal, f.setOf("goal"));
		return bound;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.COM008 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.COM008 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final COM008 model = new COM008();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
//			solver.options().setSymmetryBreaking(22);
//			solver.options().setFlatten(false);
			final Formula f = model.checkGoalToBeProved();
			final Bounds b = model.bounds(n);
//			System.out.println(f);
			
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
