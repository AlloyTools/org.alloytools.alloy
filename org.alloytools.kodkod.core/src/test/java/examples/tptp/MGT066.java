package examples.tptp;

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
import kodkod.instance.Universe;

/**
 * A KK encoding of MGT066+1.p from http://www.cs.miami.edu/~tptp/
 * 
 * @author Emina Torlak
 */
public final class MGT066 {
	private Relation lt, leq, gt, geq;
	
	/**
	 * Constructs a new instance of MGT066.
	 */
	public MGT066() {
		super();
		lt = Relation.binary("smaller");
		leq = Relation.binary("smaller_or_equal");
		gt = Relation.binary("greater");
		geq = Relation.binary("greater_or_equal");
	}

	/**
	 * Returns the definition_smaller_or_equal axiom.
	 * @return definition_smaller_or_equal
	 */
	public final Formula definitionSmallerOrEqual() {
		return leq.eq(lt.union(Expression.IDEN));
	}
	
	/**
	 * Returns the definition_greater_or_equal axiom.
	 * @return definition_greater_or_equal
	 */
	public final Formula definitionGreaterOrEqual() {
		return geq.eq(gt.union(Expression.IDEN));
	}
	
	/**
	 * Returns definition_smaller axiom.
	 * @return definition_smaller
	 */
	public final Formula definitionSmaller() {
		return lt.eq(gt.transpose());
	}
	
	/**
	 * Returns meaning_postulate_greater_strict axiom.
	 * @return meaning_postulate_greater_strict
	 */
	public final Formula meaningPostulateGreaterStrict() {
		return gt.intersection(gt.transpose()).no();
	}
	
	/**
	 * Returns meaning_postulate_greater_transitive
	 * @return meaning_postulate_greater_transitive
	 */
	public final Formula meaningPostulateGreaterTransitive() {
		return (gt.join(gt)).in(gt);
	}
	
	/**
	 * Returns meaning_postulate_greater_comparable
	 * @return meaning_postulate_greater_comparable
	 */
	public final Formula meaningPostulateGreaterComparable() {
		final Variable x = Variable.unary("X");
		final Variable y = Variable.unary("Y");
		return x.eq(y).or(y.in(x.join(lt))).or(x.in(y.join(lt))).forAll(x.oneOf(Expression.UNIV).and(y.oneOf(Expression.UNIV)));
	}
	
	/**
	 * Returns the conjunction of all axioms.
	 * @return conjunction of all axioms
	 */
	public final Formula axioms() { 
		return definitionSmaller().and(definitionSmallerOrEqual()).and(definitionGreaterOrEqual())
			.and(meaningPostulateGreaterComparable()).and(meaningPostulateGreaterStrict()).and(meaningPostulateGreaterTransitive());
	}
	/**
	 * Returns a bounds for a universe of the given size.
	 * @return bounds for a universe of the given size.
	 */
	public final Bounds bounds(int size) {
		assert size > 0;
		final List<String> atoms = new ArrayList<String>(size);
		for(int i = 0; i < size; i++)
			atoms.add("a"+i);
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		b.bound(lt, f.allOf(2));
		b.bound(leq, f.allOf(2));
		b.bound(gt, f.allOf(2));
		b.bound(geq, f.allOf(2));
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.MGT066 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.MGT066 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final MGT066 model = new MGT066();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setSymmetryBreaking(n*n);
			final Formula f = model.axioms();
			final Bounds b = model.bounds(n);
			System.out.println(f);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
