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
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A KK encoding of LAT258+1.p from http://www.cs.miami.edu/~tptp/
 * @author Emina Torlak
 */
public final class LAT258 {
	private final Relation goal, p, t, u, v, w, x, y, z;
	private final Relation lessThan, meet, join;
	/**
	 * Constructs a new instance of LAT258.
	 */
	public LAT258() {
		goal = Relation.unary("goal");
		p = Relation.unary("p");
		t = Relation.unary("t");
		u = Relation.unary("u");
		v = Relation.unary("v");
		w = Relation.unary("w");
		x = Relation.unary("x");
		y = Relation.unary("y");
		z = Relation.unary("z");
		lessThan = Relation.binary("lessThan");
		meet = Relation.ternary("meet");
		join = Relation.ternary("join");
	}

	/**
	 * Returns function declarations.
	 * @return function declarations
	 */
	public final Formula decls() {
		return p.one().and(t.one()).and(v.one()).and(w.one()).
		       and(u.one()).and(x.one()).and(y.one()).and(z.one());
	}

	/**
	 * Returns the join_assumption axiom.
	 * @return join_assumption axiom.
	 */
	public final Formula joinAssumption() {
		// x->y->t + x->z->u in join 
		return x.product(y).product(t).union(x.product(z).product(u)).in(join);
	}
	
	
	/**
	 * Returns the meet_assumption axiom.
	 * @return the meet_assumption axiom.
	 */
	public final Formula meetAssumption() {
		// t->u->v in meet
		return t.product(u).product(v).in(meet);
	}
	
	/**
	 * Returns the meet_join_assumption axiom.
	 * @return the meet_join_assumption axiom.
	 */
	public final Formula meetJoinAssumption() { 
		// y->z->w in meet && x->w->p in join
		return y.product(z).product(w).in(meet).and(x.product(w).product(p).in(join));
	}
	
	/**
	 * Returns the goal_ax axiom.
	 * @return the goal_ax axiom.
	 */
	public final Formula goalAx() {
		// v->p in lessThan => some goal
		return v.product(p).in(lessThan).implies(goal.some());
	}
	
	/**
	 * Returns the less_than_reflexive axiom.
	 * @return the less_than_reflexive axiom.
	 */
	public final Formula lessThanReflexive() { 
		// iden in lessThan
		return Expression.IDEN.in(lessThan);
	}

	/**
	 * Returns the less_than_transitive axiom.
	 * @return the less_than_transitive axiom.
	 */
	public final Formula lessThanTransitive() {
		// lessThan.lessThan in lessThan
		return lessThan.join(lessThan).in(lessThan);
	}
	
	/**
	 * Returns the lower_bound_meet axiom.
	 * @return the lower_bound_meet axiom.
	 */
	public final Formula lowerBoundMeet() {
		final Variable c = Variable.unary("C");
		final Expression e0 = c.join(lessThan);
		final Formula f0 = meet.join(c).in(e0.product(e0));
		// all c: univ | meet.c in c.lessThan->c.lessThan
		return f0.forAll(c.oneOf(UNIV));
	}
	
	/*
	 * fof(greatest_lower_bound_meet,axiom,(
    ! [A,B,C,D] : 
      ( ( meet(A,B,C)
        & less_than(D,A)
        & less_than(D,B) )
     => less_than(D,C) ) )).
	 */
	/**
	 * Returns the greatest_lower_bound_meet axiom.
	 * @return the greatest_lower_bound_meet axiom.
	 */
	public final Formula greatestLowerBoundMeet() {
		final Variable a = Variable.unary("A"), b = Variable.unary("B");
		final Expression e0 = b.join(a.join(meet));
		final Formula f0 = e0.some().implies(lessThan.join(a).intersection(lessThan.join(b)).in(lessThan.join(e0)));
		return f0.forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns the upper_bound_join axiom.
	 * @return the upper_bound_join axiom.
	 */
	public final Formula upperBoundJoin() {
		final Variable c = Variable.unary("C");
		final Expression e0 = lessThan.join(c);
		final Formula f0 = join.join(c).in(e0.product(e0));
		// all c: univ | join.c in lessThan.c->lessThan.c
		return f0.forAll(c.oneOf(UNIV));
	}
	
	/**
	 * Returns the least_upper_bound_join axiom.
	 * @return the least_upper_bound_join axiom.
	 */
	public final Formula leastUpperBoundJoin() {
		final Variable a = Variable.unary("A"), b = Variable.unary("B");
		final Expression e0 = b.join(a.join(meet));
		final Formula f0 = e0.some().implies(a.join(lessThan).intersection(b.join(lessThan)).in(e0.join(lessThan)));
		return f0.forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
	}
	
	/**
	 * Returns the less_than_meet_join axiom.
	 * @return the less_than_meet_join axiom.
	 */
	public final Formula lessThanMeetJoin() {
		final Variable a = Variable.unary("A");
		final Variable b = Variable.unary("B");
		final Expression e0 = a.product(b);
		final Formula f0 = e0.product(a).in(meet);
		final Formula f1 = e0.product(b).in(join);
		// all a: univ, b: a.lessThan | a->b->a in meet && a->b->b in join
		return f0.and(f1).forAll(b.oneOf(a.join(lessThan))).forAll(a.oneOf(UNIV));
	}
	
	/**
	 * Assumes that e is a ternary relation.
	 * @return e.univ~ in e.univ
	 */
	private final Formula commutative(Expression e) {
		final Expression first2 = e.join(UNIV);
		return first2.transpose().in(first2);
	}
	
	/**
	 * Returns the commutitivity_meet axiom.
	 * @return the commutitivity_meet axiom.
	 */
	public final Formula commutativityMeet() {
		return commutative(meet);
	}
	
	/**
	 * Returns the commutitivity_join axiom.
	 * @return the commutitivity_join axiom.
	 */
	public final Formula commutativityJoin() {
		return commutative(join);
	}
	
	/*
	 * fof(associativity_meet,axiom,(
    ! [A,B,C,D,E,F] : 
      ( ( meet(A,B,D)
        & meet(D,C,E)
        & meet(B,C,F) )
     => meet(A,F,E) ) )).
	 */
	/**
	 * Assumes that r is a ternary relation.
	 * @return all a, b, c: univ | a->(c.(b.r))->(c.(d.r)) in r
	 */
	private final Formula associative(Expression r) {
		final Variable a = Variable.unary("A"), b = Variable.unary("B"), c = Variable.unary("C");
		final Expression d = b.join(a.join(r));
		final Expression e = c.join(d.join(r));
		final Expression f = c.join(b.join(r));
		final Formula f0 = a.product(f).product(e).in(r);
		// all a, b, c: univ | a->(c.(b.r))->(c.((b.(a.r)).r)) in r
		return f0.forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}
	
	/**
	 * Returns the associativity_meet axiom.
	 * @return the associativity_meet axiom.
	 */
	public final Formula associativityMeet() {
		return associative(meet);
	}
	
	/**
	 * Returns the associativity_join axiom.
	 * @return the associativity_ axiom.
	 */
	public final Formula associativityJoin() {
		return associative(join);
	}
	
	
	/**
	 * Returns the lo_le_distr axiom.
	 * @return the lo_le_distr axiom.
	 */
	public final Formula loLeDistr() {
		final Variable a = Variable.unary("A"), b = Variable.unary("B"), c = Variable.unary("C");
		final Expression h = c.join(b.join(join));
		final Expression d = h.join(a.join(meet));
		final Expression e = b.join(a.join(meet));
		final Expression f = c.join(a.join(meet));
		final Expression g = f.join(e.join(join));
		final Formula f0 = d.product(g).in(lessThan);
		// all a, b, c: univ | (c.(b.(meet))).(a.meet) -> (c.(a.meet)).((b.(a.meet)).join) in lessThan
		return f0.forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)));
	}
	
	/**
	 * Returns the do_lattice axiom.
	 * @return the do_lattice axiom.
	 */
	public final Formula doLattice() {
		return UNIV.product(UNIV).in(meet.join(UNIV));
	}
	
	/**
	 * Returns the goal_to_be_proved conjecture.
	 * @return goal_to_be_proved conjecture.
	 */
	public final Formula goalToBeProved() { 
		return goal.some();
	}
	
	/**
	 * Returns the conjunction of all decls and axioms.
	 * @return the conjunction of all decls and axioms. 
	 */
	public final Formula axioms() {
		return decls().and(joinAssumption()).and(meetAssumption()).
		       and(meetJoinAssumption()).and(goalAx()).and(lessThanReflexive()).
		       and(lessThanTransitive()).and(lowerBoundMeet()).
		       and(greatestLowerBoundMeet()).and(upperBoundJoin()).
		       and(leastUpperBoundJoin()).and(lessThanMeetJoin()).
		       and(commutativityMeet()).and(commutativityJoin()).
		       and(associativityMeet()).and(associativityJoin()).
		       and(loLeDistr()).and(doLattice());
	}
	/**
	 * Returns the conjunction of the axioms and the negation of the hypothesis.
	 * @return axioms() && !goalToBeProved()
	 */
	public final Formula checkGoalToBeProved() { 
		return axioms().and(goalToBeProved().not());
	}
	/**
	 * Returns the bounds for the given scope.
	 * @return the bounds for the given scope.
	 */
	public final Bounds bounds(int n) {
		assert n > 0;
		final List<String> atoms = new ArrayList<String>(n);
		for(int i = 0; i < n; i++)
			atoms.add("n"+i);
		final Universe univ = new Universe(atoms);
		final TupleFactory f = univ.factory();
		final Bounds b = new Bounds(univ);
		b.bound(goal, f.setOf("n0"));
		final TupleSet all1 = f.allOf(1);
		b.bound(p, all1);
		b.bound(t, all1);
		b.bound(v, all1);
		b.bound(w, all1);
		b.bound(u, all1);
		b.bound(x, all1);
		b.bound(y, all1);
		b.bound(z, all1);
		b.bound(lessThan, f.allOf(2));
		final TupleSet all3 = f.allOf(3);
		b.bound(join, all3);
		b.bound(meet, all3);
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.LAT258 [scope]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.LAT258 [scope]
	 */
	public  static void main(String[] args) {
		if (args.length < 1)
			usage();
		try {

			final int n = Integer.parseInt(args[0]);
			final LAT258 model = new LAT258();
			
			final Bounds b = model.bounds(n);
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			
			final Formula f = model.checkGoalToBeProved();
			System.out.println(f);
//			System.out.println(b);
			final Solution s = solver.solve(f, b);
			System.out.println(s);
		
	
		} catch (NumberFormatException nfe) {
			usage();
		} catch (HigherOrderDeclException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnboundLeafException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
	}
}
