/**
 * 
 */
package examples.tptp;
import static kodkod.ast.Expression.UNIV;

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
import kodkod.instance.Universe;

/**
 * A KK encoding of ALG212+1.p from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public final class ALG212 {
	private final Relation f;
	
	/**
	 * Constucts a new instance of ALG212.
	 */
	public ALG212() {
		f = Relation.nary("f", 4);
	}
	
	/**
	 * Returns the declarations.
	 * @return declarations.
	 */
	public final Formula decls() {
		// all x,y,z: univ | one f[x][y][z] 
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Variable z = Variable.unary("z");
		final Formula f0 = z.join(y.join(x.join(f))).one();
		return f0.forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns the majority axiom.
	 * @return majority
	 */
	public final Formula majority() {
		// all x, y: A | f[x][x][y] = x
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		return y.join(x.join(x.join(f))).eq(x).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)));
	}
	
	/**
	 * Returns the permute1 axiom.
	 * @return permute1
	 */
	public final Formula permute1() {
		// all x, y, z: A | f[x][y][z] = f[z][x][y]
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Variable z = Variable.unary("z");
		final Formula f0 = z.join(y.join(x.join(f))).eq(y.join(x.join(z.join(f))));
		return f0.forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns the permute2 axiom.
	 * @return permute2
	 */
	public final Formula permute2() {
		// all x, y, z: A | f[x][y][z] = f[x][z][y]
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Variable z = Variable.unary("z");
		final Formula f0 = z.join(y.join(x.join(f))).eq(y.join(z.join(x.join(f))));
		return f0.forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns the associativity axiom.
	 * @return associativity
	 */
	public final Formula associativity() {
		// all w, x, y, z: A | f[f[x][w][y]][w][z] = f[x][w][f[y][w][z]]
		final Variable w = Variable.unary("w");
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Variable z = Variable.unary("z");
		final Expression e0 = y.join(w.join(x.join(f)));
		final Expression e1 = z.join(w.join(e0.join(f)));
		final Expression e2 = z.join(w.join(y.join(f)));
		final Expression e3 = e2.join(w.join(x.join(f)));
		return e1.eq(e3).forAll(w.oneOf(UNIV).and(x.oneOf(UNIV)).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns the conjuction of all axioms.
	 * @return axioms
	 */
	public final Formula axioms() { 
		return decls().and(majority()).and(permute1()).and(permute2()).and(associativity());
	}
	
	/**
	 * Returns the dist_long conjecture.
	 * @return dist_long
	 */
	public final Formula distLong() {
		// all u, w, x, y, z: A | f[f[x][y][z]][u][w] = f[f[x][u][w]][f[y][u][w]][f[z][u][w]]
		final Variable u = Variable.unary("u");
		final Variable w = Variable.unary("w");
		final Variable x = Variable.unary("x");
		final Variable y = Variable.unary("y");
		final Variable z = Variable.unary("z");
		final Expression e0 =  z.join(y.join(x.join(f)));
		final Expression e1 = w.join(u.join(e0.join(f)));
		final Expression e2 = w.join(u.join(x.join(f)));
		final Expression e3 = w.join(u.join(y.join(f)));
		final Expression e4 = w.join(u.join(z.join(f)));
		final Expression e5 = e4.join(e3.join(e2.join(f)));
		return e1.eq(e5).
		  forAll(u.oneOf(UNIV).and(w.oneOf(UNIV)).and(x.oneOf(UNIV)).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
	}
	
	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !distLong()
	 */
	public final Formula checkDistLong() { 
		return axioms().and(distLong().not());
	}
	
	/**
	 * Returns the bounds for the given scope.
	 * @return bounds for the given scope
	 */
	public final Bounds bounds(int n) {
		assert n > 0;
		final List<String> atoms = new ArrayList<String>(n);
		for(int i = 0; i < n; i++) atoms.add("a"+i);
		final Universe u = new Universe(atoms);
		final Bounds b = new Bounds(u);
		b.bound(f, u.factory().allOf(4));
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.ALG212 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.ALG212 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final ALG212 model = new ALG212();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
//			solver.options().setSymmetryBreaking(n*n);
//			solver.options().setFlatten(false);
			final Formula f = model.checkDistLong();
			final Bounds b = model.bounds(n);
			System.out.println(f);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
