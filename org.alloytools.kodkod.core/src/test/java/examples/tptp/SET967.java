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
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * A KK encoding of SET967+1.p from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public final class SET967 {

	private final Relation empty;
	private final Relation subset, in, disjoint, union, singleton;
	private final Relation intersect2, union2, cartesian2, ordered, unordered;
	
	/**
	 * Constructs a new instance of SET967.
	 */
	public SET967() {
		empty = Relation.unary("empty");
		subset = Relation.binary("subset");
		in = Relation.binary("in");
		disjoint = Relation.binary("disjoint");
		union = Relation.binary("union");
		singleton = Relation.binary("singleton");
		intersect2 = Relation.ternary("set_intersection2");
		union2 = Relation.ternary("set_union2");
		cartesian2 = Relation.ternary("cartesian_product2");
		ordered =  Relation.ternary("ordered_pair");
		unordered =  Relation.ternary("unordered_pair");
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
	 * Returns cartesian_product2[A][B]
	 * @return cartesian_product2[A][B]
	 */
	final Expression cartesian_product2(Expression a, Expression b) {
		return b.join(a.join(cartesian2));
	}
	
	/**
	 * Returns ordered_pair[A][B]
	 * @return ordered_pair[A][B]
	 */
	final Expression ordered_pair(Expression a, Expression b) {
		return b.join(a.join(ordered));
	}
	
	/**
	 * Returns unordered_pair[A][B]
	 * @return unordered_pair[A][B]
	 */
	final Expression unordered_pair(Expression a, Expression b) {
		return b.join(a.join(unordered));
	}
	
	/**
	 * Returns union[a]
	 * @return union[a]
	 */
	final Expression union(Expression a) { 
		return a.join(union);
	}
	
	/**
	 * Returns singleton[a]
	 * @return singleton[a]
	 */
	final Expression singleton(Expression a) { 
		return a.join(singleton);
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
		final Formula f1 = singleton.function(UNIV, UNIV);
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Formula f2 = set_intersection2(a, b).one();
		final Formula f3 = set_union2(a, b).one();
		final Formula f4 = cartesian_product2(a,b).one();
		final Formula f5 = ordered_pair(a, b).one();
		final Formula f6 = unordered_pair(a, b).one();
		return f0.and(f1).and(f2.and(f3).and(f4).and(f5).and(f6).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV))));
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
	 * Returns commutativity_k2_tarski axiom.
	 * @return commutativity_k2_tarski
	 */
	public final Formula commutativity_k2_tarski() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return unordered_pair(a, b).eq(unordered_pair(b, a)).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
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
	 * Returns d5_tarski axiom.
	 * @return d5_tarski
	 */
	public final Formula d5_tarski() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return ordered_pair(a,b).eq(unordered_pair(unordered_pair(a, b), singleton(a))).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns fc1_misc_1 axiom.
	 * @return fc1_misc_1
	 */
	public final Formula fc1_misc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		return empty(ordered_pair(a, b)).not().forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
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
	 * Returns 155_zfmisc_1 axiom.
	 * @return 155_zfmisc_1
	 */
	public final Formula a155_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		final Variable d = Variable.unary("D");
		final Formula f0 = in(ordered_pair(a, b), cartesian_product2(c, d));
		final Formula f1 = in(a,c).and(in(b,d));
		return f0.iff(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)).and(d.oneOf(UNIV)));
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
	 * Returns t102_zfmisc_1 axiom.
	 * @return t102_zfmisc_1
	 */
	public final Formula t102_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		return in(a,cartesian_product2(b, c)).implies(ordered.join(a).some()).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}
	
	/**
	 * Returns t107_zfmisc_1 axiom.
	 * @return t107_zfmisc_1
	 */
	public final Formula t107_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		final Variable d = Variable.unary("D");
		final Formula f0 = in(ordered_pair(a, b), cartesian_product2(c, d));
		final Formula f1 = in(ordered_pair(b, a), cartesian_product2(d, c));
		return f0.iff(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)).and(d.oneOf(UNIV)));
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
	 * Returns t112_zfmisc_1 axiom.
	 * @return t112_zfmisc_1
	 */
	public final Formula t112_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		final Variable d = Variable.unary("D");
		final Formula f0 = in(c,a).implies(ordered.join(c).some()).forAll(c.oneOf(UNIV));
		final Formula f1 = in(c,b).implies(ordered.join(c).some()).forAll(c.oneOf(UNIV));
		final Formula f2 = in(ordered_pair(c,d),a).iff(in(ordered_pair(c,d),b)).forAll(c.oneOf(UNIV).and(d.oneOf(UNIV)));
		return f0.and(f1).and(f2).implies(a.eq(b)).
			forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	/**
	 * Returns the conjunction of all  axioms.
	 * @return conjunction of all  axioms.
	 */
	public final Formula axioms() {
		return decls().and(antisymmetry_r2_hidden()).and(commutativity_k2_xboole_0()).
		and(commutativity_k2_tarski()).and(d2_xboole_0()).and(d5_tarski()).
		and(fc1_misc_1()).and(fc2_xboole_0()).and(fc3_xboole_0()).and(idempotence_k2_xboole_0()).
		and(a155_zfmisc_1()).and(rc1_xboole_0()).and(rc2_xboole_0()).
		and(t102_zfmisc_1()).and(t107_zfmisc_1()).and(t4_xboole_0()).
		and(t112_zfmisc_1());
	}
	
	/**
	 * Returns t120_zfmisc_1 conjecture.
	 * @return t120_zfmisc_1
	 */
	public final Formula t120_zfmisc_1() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Variable c = Variable.unary("C");
		final Formula f0 = cartesian_product2(set_union2(a, b), c).eq(set_union2(cartesian_product2(a, c), cartesian_product2(b, c)));
		final Formula f1 = cartesian_product2(c,set_union2(a,b)).eq( set_union2(cartesian_product2(c,a),cartesian_product2(c,b)));
		return f0.and(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}
	
	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !t120_zfmisc_1()
	 */
	public final Formula checkT120_zfmisc_1() { 
		return axioms().and(t120_zfmisc_1().not());
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
		b.bound(singleton, f.allOf(2));
		b.bound(intersect2, f.allOf(3));
		b.bound(cartesian2, f.allOf(3));
		b.bound(union2, f.allOf(3));
		b.bound(ordered, f.allOf(3));
		b.bound(unordered, f.allOf(3));
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.SET967 [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.SET967 [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final SET967 model = new SET967();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
//			solver.options().setSymmetryBreaking(n*n);
//			solver.options().setFlatten(false);
			final Formula f = model.checkT120_zfmisc_1();
			final Bounds b = model.bounds(n);
			System.out.println(f);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}

