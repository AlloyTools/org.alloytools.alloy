package kodkod.examples.csp;

import static kodkod.ast.Expression.UNIV;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * A KK encoding of the Latin squares problem.
 * 
 * @author Emina Torlak
 */
public final class LatinSquare {
	private final Relation square;
	
	/**
	 * Constructs a model of a Latin square.
	 */
	public LatinSquare() {
		square = Relation.ternary("square");
	}

	/**
	 * Returns a KK encoding of the qg5 problem (http://4c.ucc.ie/~tw/csplib/prob/prob003/spec.html)
	 * 
	 * @return a KK encoding of the qg5 problem.
	 */
	public final Formula qg5() {
		//((b*a)*b)*b = a.
		final Variable a = Variable.unary("a");
		final Variable b = Variable.unary("b");
		final Expression e0 = a.join(b.join(square)); // b*a
		final Expression e1 = b.join(e0.join(square)); // (b*a)*b
		final Expression e2 = b.join(e1.join(square)); // ((b*a)*b)*b
		return e2.intersection(a).some().forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns a formula stating that the square relation is a latin square.
	 * @return a formula stating that the square relation is a latin square.
	 */
	public final Formula latin() {
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Formula f0 = y.join(x.join(square)).one().forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)));
		final Variable z = Variable.unary("z");
		final Formula row = UNIV.in(UNIV.join(z.join(square)));
		final Formula col = UNIV.in(z.join(UNIV.join(square)));
		return f0.and((row.and(col)).forAll(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns a formula stating that the square relation is idempotent.
	 * @return a formula stating that the square relation is idempotent.
	 */
	public final Formula idempotent() {
		final Variable x = Variable.unary("x");
		return x.product(x).product(x).in(square).forAll(x.oneOf(UNIV));
	}
	
	/**
	 * Returns the bounds for a Latin square of the given order.
	 * @requires n > 0
	 * @return the bounds for a Latin square of the given order.
	 */
	public final Bounds bounds(int n) {
		assert n>0;
		final List<String> nums = new ArrayList<String>(n);
		for(int i = 0; i < n; i++)
			nums.add(String.valueOf(i));
		final Universe u = new Universe(nums);
		final Bounds b = new Bounds(u);
		final TupleFactory f = u.factory();
		b.bound(square, f.allOf(3));
		return b;
	}
		
	private static void usage() {
		System.out.println("java examples.LatinSquare [order]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.LatinSquare [order]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final LatinSquare model = new LatinSquare();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setSymmetryBreaking(n*n*n);
			final Formula f = model.latin().and(model.qg5()).and(model.idempotent());
			final Bounds b = model.bounds(n);
			System.out.println(f); 
			final Solution sol = solver.solve(f, b);
			if (sol.instance()==null) {
				System.out.println(sol);
			} else {
				System.out.println(sol.stats());
				final Iterator<Tuple> iter = sol.instance().tuples(model.square).iterator();
				for(int i = 0; i < n; i++) {
					for(int j = 0; j < n; j++) {
						System.out.print(iter.next().atom(2));
						System.out.print("\t");
					}
					System.out.println();
				}
			}
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
