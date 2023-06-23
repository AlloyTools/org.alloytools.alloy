package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;


public class DiningP extends DModel {

	final private Universe u;


	final private Relation Phil,Fork,lFork,rFork, taken, state_first, state_next, state_last, State;	
	private int n_ps, n_ts;


	public DiningP(String[] args) {

		Phil = Relation.unary("Phil");
		Fork = Relation.unary("Forks");
		rFork = Relation.binary("rForks");
		lFork = Relation.binary("lForks");
		taken = Relation.nary("taken",3);

		State = Relation.unary("State");
		state_first = Relation.unary("so/Ord.First");
		state_next = Relation.binary("so/Ord.Next");
		state_last = Relation.unary("");
		
		n_ps = Integer.valueOf(args[0]);
		n_ts = Integer.valueOf(args[1]);

		final List<Object> atoms = new ArrayList<Object>(2*n_ps+n_ts);
		
		for (int i = 0; i < n_ps; i++) 
			atoms.add("P" + i);
		
		for (int i = 0; i < n_ps; i++) 
			atoms.add("F" + i);

		for (int i = 0; i < n_ts; i++) 
			atoms.add("State" + i);
		
		u = new Universe(atoms);
	}


	public Formula partition1() {
		final Formula f1 = lFork.function(Phil, Fork);
		final Formula f2 = rFork.function(Phil, Fork);
		Variable x = Variable.unary("x");
		final Formula f3 = (x.join(rFork).eq(x.join(lFork))).not().forAll(x.oneOf(Phil));
		Variable z = Variable.unary("y");
		Variable y = Variable.unary("z");
		final Formula f4 = (y.join(rFork).eq(z.join(rFork))).implies(y.eq(z)).forAll(y.oneOf(Phil).and(z.oneOf(Phil)));
		Variable a = Variable.unary("a");
		Variable b = Variable.unary("b");
		final Formula f5 = (a.join(lFork).eq(b.join(lFork))).implies(a.eq(b)).forAll(a.oneOf(Phil).and(b.oneOf(Phil)));

		return Formula.and(f1,f2,f3,f4,f5);
	}

	private Formula TakeLeft(Expression t, Expression p, Expression f) {
		Formula f1 = f.in((taken.join(t)).join(Phil)).not();
		Formula f2 = p.join(lFork).eq(f);
		Formula f3 = taken.join(t.join(state_next)).eq(taken.join(t).union(f.product(p)));

		return Formula.and(f1,f2,f3);
	}

	private Formula TakeRight(Expression t, Expression p, Expression f) {
		Formula f1 = f.in((taken.join(t)).join(Phil)).not();
		Formula f2 = p.join(rFork).eq(f);
		Formula f3 = taken.join(t.join(state_next)).eq(taken.join(t).override(f.product(p)));

		return Formula.and(f1,f2,f3);
	}

	private Formula Drop(Expression t, Expression p, Expression f) {
		Formula f1 = f.in((taken.join(t)).join(Phil));
		Formula f2 = f.join(taken.join(t)).eq(p);
		Formula f3 = taken.join(t.join(state_next)).eq(taken.join(t).difference(f.product(p)));

		return Formula.and(f1,f2,f3);

	}

	private Formula init() {
		Formula x156=taken.join(state_first).no();
		return x156;
	}
	
	private Formula next() {
		Variable t=Variable.unary("t");
		Expression x167=state_first.join(state_next.closure().union(Expression.IDEN.intersection(State.product(State))));
		Variable p=Variable.unary("p");
		Variable f=Variable.unary("f");

		Formula x189=TakeLeft(t,p,f).or(TakeRight(t,p,f)).or(Drop(t,p,f));
		Formula x181=x189.forSome((p.oneOf(Phil)).and(f.oneOf(Fork)));
		Formula next=x181.forAll(t.oneOf(x167.difference(state_last)));
		return next;
	}

	public Formula partition2() {
		Formula x97 = state_next.totalOrder(State,state_first,state_last);
		Variable t=Variable.unary("t");
		Variable f=Variable.unary("f");

		Formula x98 = (f.join(taken.join(t))).lone().forAll(f.oneOf(Fork).and(t.oneOf(State)));
		
		return Formula.compose(FormulaOperator.AND, x97, x98, init(), next());
	}
	/**
	 * Returns a bounds for the given number of persons.
	 * 
	 * @return a bounds for the given number of persons.
	 */
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet pb = f.range(f.tuple("P0"), f.tuple("P"+ (n_ps-1)));
		final TupleSet fb = f.range(f.tuple("F0"), f.tuple("F"+ (n_ps-1)));

		b.boundExactly(Fork, fb);
		b.boundExactly(Phil, pb);
		b.bound(rFork, pb.product(fb));
		b.bound(lFork, pb.product(fb));

		return b;
	}

	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final TupleSet pb = f.range(f.tuple("P0"), f.tuple("P"+ (n_ps-1)));
		final TupleSet fb = f.range(f.tuple("F0"), f.tuple("F"+ (n_ps-1)));
		final TupleSet sb = f.range(f.tuple("State0"), f.tuple("State"+ (n_ts-1)));

		b.boundExactly(State, sb);
		b.bound(state_first, sb);
		b.bound(state_next, sb.product(sb));
		b.bound(state_last, sb);

		b.bound(taken, fb.product(pb).product(sb));

		return b;
	}

	@Override
	public int getBitwidth() {
		return 1;
	}


	public String toString() {
		StringBuilder sb = new StringBuilder("Dining");
		sb.append("-");
		sb.append(n_ps);		
		sb.append("-");
		sb.append(n_ts);		
		return sb.toString();
	}


	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
}
