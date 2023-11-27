/**
 * 
 */
package kodkod.examples.tptp;

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
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * A KK encoding of SET948+1.p from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public final class SET948 {
	
	private final Relation empty;
	private final Relation subset, in, disjoint, union;
	private final Relation intersect2, union2;
	
	/**
	 * Constructs a new instance of SET948.
	 */
	public SET948() {
		empty = Relation.unary("empty");
		subset = Relation.binary("subset");
		in = Relation.binary("in");
		disjoint = Relation.binary("disjoint");
		union = Relation.binary("union");
		intersect2 = Relation.ternary("set_intersection2");
		union2 = Relation.ternary("set_union2");
	}
	
	/**
	 * Returns set_intersection2[A][B]
	 * @return set_intersection2[A][B]
	 */
	final Expression set_intersection2(Expression a, Expression b) {
		return b.join(a.join(intersect2));
	}
	/**
	 * Returns set_union2[A][B]
	 * @return set_union2[A][B]
	 */
	final Expression set_union2(Expression a, Expression b) {
		return b.join(a.join(union2));
	}
	
	/**
	 * Returns union[a]
	 * @return union[a]
	 */
	final Expression union(Expression a) { 
		return a.join(union);
	}
	
	/**
	 * Returns a in empty
	 * @return a in empty
	 */
	final Formula empty(Expression a) {
		return a.in(empty);
	}
	
	/**
	 * Returns a->b in subset.
	 * @return a->b in subset.
	 */
	final Formula subset(Expression a, Expression b) {
		return a.product(b).in(subset);
	}
	
	/**
	 * Returns a->b in in.
	 * @return a->b in in
	 */
	final Formula in(Expression a, Expression b) {
		return a.product(b).in(in);
	}
	
	/**
	 * Returns a->b in disjoint.
	 * @return a->b in disjoint
	 */
	final Formula disjoint(Expression a, Expression b) {
		return a.product(b).in(disjoint);
	}
	
	
	/**
	 * Returns the declarations.
	 * @return declarations
	 */
	public final Formula decls() { 
		final Formula f0 = union.function(UNIV, UNIV);
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Formula f1 = set_intersection2(a, b).one();
		final Formula f2 = set_union2(a, b).one();
		return f0.and(f1.and(f2).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV))));
	}
	
	/**
	 * Returns antisymmetry_r2_hidden axiom.
	 * @return antisymmetry_r2_hidden
	 */
	public final Formula antisymmetry_r2_hidden() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return in(a,b).implies(in(b,a).not()).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns commutativity_k2_xboole_0 axiom.
	 * @return commutativity_k2_xboole_0
	 */
	public final Formula commutativity_k2_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return set_union2(a, b).eq(set_union2(b, a)).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns d10_xboole_0 axiom.
	 * @return d10_xboole_0
	 */
	public final Formula d10_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return a.eq(b).iff(subset(a,b).and(subset(b,a))).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns d2_xboole_0 axiom.
	 * @return d2_xboole_0
	 */
	public final Formula d2_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		return c.eq(set_union2(a, b)).iff(in.join(c).eq(in.join(a).union(in.join(b)))).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}

	/**
	 * Returns d3_tarski axiom.
	 * @return d3_tarski
	 */
	public final Formula d3_tarski() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return subset(a,b).iff(in.join(a).in(in.join(b))).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns d3_xboole_0 axiom.
	 * @return d3_xboole_0
	 */
	public final Formula d3_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		return c.eq(set_intersection2(a, b)).iff(in.join(c).eq(in.join(a).intersection(in.join(b)))).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}
	
	/**
	 * Returns d4_tarski axiom.
	 * @return d4_tarski
	 */
	public final Formula d4_tarski() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return b.eq(union(a)).iff(in.join(b).eq(in.join(in.join(a)))).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns fc2_xboole_0 axiom.
	 * @return fc2_xboole_0
	 */
	public final Formula fc2_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return empty(a).not().implies(empty(set_union2(a, b)).not()).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns fc3_xboole_0 axiom.
	 * @return fc3_xboole_0
	 */
	public final Formula fc3_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return empty(a).not().implies(empty(set_union2(b, a)).not()).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns idempotence_k2_xboole_0 axiom.
	 * @return idempotence_k2_xboole_0
	 */
	public final Formula idempotence_k2_xboole_0() {
		final Variable a = Variable.unary("A");
		return set_union2(a, a).eq(a).forAll(a.oneOf(UNIV));
	}
	
	/**
	 * Returns idempotence_k3_xboole_0 axiom.
	 * @return idempotence_k3_xboole_0
	 */
	public final Formula idempotence_k3_xboole_0() {
		final Variable a = Variable.unary("A");
		return set_intersection2(a, a).eq(a).forAll(a.oneOf(UNIV));
	}
	
	/**
	 * Returns rc1_xboole_0 axiom.
	 * @return rc1_xboole_0
	 */
	public final Formula rc1_xboole_0() {
		return empty.some();
	}
	
	/**
	 * Returns rc2_xboole_0 axiom.
	 * @return rc2_xboole_0
	 */
	public final Formula rc2_xboole_0() {
		return UNIV.difference(empty).some();
	}
	
	/**
	 * Returns reflexivity_r1_tarski axiom.
	 * @return reflexivity_r1_tarski
	 */
	public final Formula reflexivity_r1_tarski() {
		final Variable a = Variable.unary("A");
		return subset(a,a).forAll(a.oneOf(UNIV));
	}
	
	/**
	 * Returns symmetry_r1_xboole_0 axiom.
	 * @return symmetry_r1_xboole_0
	 */
	public final Formula symmetry_r1_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return disjoint(a, b).implies(disjoint(b, a)).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns t4_xboole_0 axiom.
	 * @return t4_xboole_0
	 */
	public final Formula t4_xboole_0() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return disjoint(a, b).not().implies(set_intersection2(a, b).some()).
			and(disjoint(a, b).implies(set_intersection2(a, b).no())).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns t97_zfmisc_1 axiom.
	 * @return t97_zfmisc_1
	 */
	public final Formula t97_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return subset(union(set_intersection2(a, b)), set_intersection2(union(a), union(b))).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	/**
	 * Returns the conjunction of all  axioms.
	 * @return conjunction of all  axioms.
	 */
	public final Formula axioms() {
		return decls().and(antisymmetry_r2_hidden()).and(commutativity_k2_xboole_0()).
		and(d10_xboole_0()).and(d2_xboole_0()).and(d3_tarski()).and(d3_xboole_0()).
		and(d4_tarski()).and(fc2_xboole_0()).and(fc3_xboole_0()).and(idempotence_k2_xboole_0()).
		and(idempotence_k3_xboole_0()).and(rc1_xboole_0()).and(rc2_xboole_0()).
		and(reflexivity_r1_tarski()).and(symmetry_r1_xboole_0()).and(t4_xboole_0()).
		and(t97_zfmisc_1());
	}

	/**
	 * Returns t101_zfmisc_1 conjecture.
	 * @return t101_zfmisc_1
	 */
	public final Formula t101_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		final Variable d = Variable.unary("D");
		final Formula f0 = in(c.union(d), set_union2(a, b)).implies(c.eq(d).or(disjoint(c, c))).
			forAll(c.oneOf(UNIV).and(d.oneOf(UNIV)));
		final Formula f1 = union(set_intersection2(a, b)).eq(set_intersection2(union(a), union(b)));
		return f0.implies(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !t101_zfmisc_1()
	 */
	public final Formula checkT101_zfmisc_1() { 
		return axioms().and(t101_zfmisc_1().not());
	}
	
	/**
	 * Returns bounds for the given scope.
	 * @return bounds for the given scope.
	 */
	public final Bounds bounds(int n) {
		assert n > 0;
		final List<String> atoms = new ArrayList<String>(n);
		for(int i = 0; i < n; i++)
			atoms.add("a"+i);
		final Universe u = new Universe(atoms);
		final Bounds b = new Bounds(u);
		final TupleFactory f = u.factory();
		b.bound(empty, f.allOf(1));
		b.bound(subset, f.allOf(2));
		b.bound(in, f.allOf(2));
		b.bound(disjoint, f.allOf(2));
		b.bound(union, f.allOf(2));
		b.bound(intersect2, f.allOf(3));
		b.bound(union2, f.allOf(3));
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.SET948 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.SET948 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final SET948 model = new SET948();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
//			solver.options().setSymmetryBreaking(n*n);
//			solver.options().setFlatten(false);
			final Formula f = model.checkT101_zfmisc_1();
			final Bounds b = model.bounds(n);
			System.out.println(f);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
