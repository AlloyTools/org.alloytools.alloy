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


public class SpanP extends DModel {

	final private Universe u;
//	final private Variant2 var;
//	final private Variant1 counter;


	final private Relation Root,Process_rem,Level,State,adjacent;
	final private Relation runs,level,parent,level_first,level_next,state_first,state_next,level_last,state_last;
	private int n_ps, n_ts;
	private Variant var;


	public enum Variant {
		V1,
		V2,
		V3;
	}

	public SpanP(String[] args) {

		Root = Relation.unary("this/Root");
		Process_rem = Relation.unary("this/Process remainder");
		Level = Relation.unary("this/Lvl");
		State = Relation.unary("this/State");
		adjacent = Relation.nary("this/Process.adj", 2);
		runs = Relation.nary("this/State.runs", 2);
		level = Relation.nary("this/State.lvl", 3);
		parent = Relation.nary("this/State.parent", 3);
		level_first = Relation.unary("lo/Ord.First");
		level_next = Relation.nary("lo/Ord.Next", 2);
		state_first = Relation.unary("so/Ord.First");
		state_next = Relation.nary("so/Ord.Next", 2);
		level_last = Relation.unary("");
		state_last = Relation.unary("");

		n_ps = Integer.valueOf(args[0]);
		n_ts = Integer.valueOf(args[1]);
		var = Variant.valueOf(args[2]);

		final List<Object> atoms = new ArrayList<Object>(2*n_ps+n_ts);
		
		atoms.add("Root");
		for (int i = 1; i < n_ps; i++) 
			atoms.add("Process" + i);
		
		for (int i = 0; i < n_ps; i++) 
			atoms.add("Lvl" + i);
		
		for (int i = 0; i < n_ts; i++) 
			atoms.add("State"+i);

		u = new Universe(atoms);
	}


	public Formula partition1() {
		Expression Process = Root.union(Process_rem);

		Formula x89=level_next.totalOrder(Level,level_first,level_last);
		Formula x90=adjacent.in(Process.product(Process));
		Formula decls = x89.and(x90);

		Expression x100=Expression.IDEN.intersection(Process.product(Process));
		Expression x99=x100.intersection(adjacent);
		Formula x98=x99.no();

		Formula x110=adjacent.transpose().in(adjacent);

		Expression x116=Expression.IDEN.intersection(Process.product(Process));
		Expression x114=adjacent.closure().union(x116);
		Expression x113=Root.join(x114);
		Formula x112=Process.in(x113);
		Formula processgraph = x112.and(x110).and(x98);

		return Formula.compose(FormulaOperator.AND, decls, processgraph);
	}

	private Formula TRNop(Expression p, Expression pre, Expression post) {
		Formula x130=p.join(pre.join(level)).eq(p.join(post.join(level)));
		Formula x136=p.join(pre.join(parent)).eq(p.join(post.join(parent)));
		return x130.and(x136);
	}

	private Formula TRActPreConds(Expression p, Expression pre) {
		Formula x146=p.join(pre.join(level)).no();
		Formula x150=p.eq(Root);
		Formula x151=p.join(adjacent).join(pre.join(level)).some();
		Formula x149=x150.or(x151);
		return x146.and(x149);
	}

	private Formula TRAct(Expression p, Expression pre, Expression post) {
		Formula x173=p.join(pre.join(level)).no();
		Formula x178=p.eq(Root);
		Formula x180=p.join(post.join(level)).eq(level_first);
		Formula x184=p.join(post.join(parent)).no();
		Formula x179=x180.and(x184);
		Formula x177=x178.implies(x179);
		Variable x191=Variable.unary("TRAct_adjProc");
		Formula x195=x191.join(pre.join(level)).some();
		Formula x198=p.join(post.join(level)).eq(x191.join(pre.join(level)).join(level_next));
		Formula x202=p.join(post.join(parent)).eq(x191);
		Formula x193=x195.and(x198).and(x202);
		Formula x189=x193.forSome(x191.oneOf(p.join(adjacent)));
		Formula x187=x178.not().implies(x189);
		return x173.and(x177).and(x187);
	}

	private Formula init() {
		Formula x156=state_first.join(level).no();
		Formula x158=state_first.join(parent).no();
		return x156.and(x158);
	}

	private Formula spanTreeAtState(Expression s) {
		Expression Process = Root.union(Process_rem);

		Expression x233=s.join(parent).transpose().closure();
		Expression x236=Expression.IDEN.intersection(Process.product(Process));
		Formula x230=Process.in(Root.join(x233.union(x236)));
		Variable x240=Variable.unary("acyclic_x");
		Formula x242=x240.in(x240.join(s.join(parent).transpose().closure()));
		Formula x241=x242.not();
		Formula x238=x241.forAll(x240.oneOf(Process));
		return x230.and(x238);

	}
	
	private Formula successfulRun() {
		Formula x229=spanTreeAtState(state_last);
		Variable x249=Variable.unary("SuccessfulRun_s");
		Formula x252=spanTreeAtState(x249);
		Formula x251=x252.not();
		Formula x247=x251.forAll(x249.oneOf(State.difference(state_last)));
		return x229.and(x247);
	}

	public Formula partition2() {
		Expression Process = Root.union(Process_rem);

		// decls
		Variable x38=Variable.unary("SuccessfulRun_this");
		Variable x46=Variable.unary("v0");
		Formula x44=(x46.join(x38.join(level))).lone().forAll(x46.oneOf(Process));
		Formula x36=x44.forAll(x38.oneOf(State));

		Formula x56=level.in(State.product(Process).product(Level));

		Variable x61=Variable.unary("SuccessfulRun_this");
		Variable x69=Variable.unary("v2");
		Formula x67=(x69.join(x61.join(parent))).lone().forAll(x69.oneOf(Process));
		Formula x59=x67.forAll(x61.oneOf(State));

		Formula x57=parent.in(State.product(Process).product(Process));

		Formula x97=state_next.totalOrder(State,state_first,state_last);

		Formula decls = x36.and(x56).and(x59).and(x97).and(x57);

		// trans if possible
		Variable x120=Variable.unary("SuccessfulRun_s");
		Expression x121=State.difference(state_last);
		Variable x128=Variable.unary("SuccessfulRun_p");
		Formula x129=TRNop(x128, x120, x120.join(state_next));
		Formula x126=x129.forAll(x128.oneOf(Process));
		Variable x143=Variable.unary("SuccessfulRun_p");
		Formula x145=TRActPreConds(x143,x120);
		Formula x144=x145.not();
		Formula x141=x144.forAll(x143.oneOf(Process));
		Formula x124=x126.implies(x141);
		Formula transifpossible=x124.forAll(x120.oneOf(x121));

		// legal trans
		Formula x155=init();
		Variable x162=Variable.unary("SuccessfulRun_s");
		Variable x166=Variable.unary("SuccessfulRun_p");
		Formula x169=x166.in(x162.join(runs));
		Expression x183=x162.join(state_next);
		Formula x172=TRAct(x166,x162,x183);
		Formula x205=TRNop(x166, x162, x183);
		Formula x171=x172.or(x205);
		Formula x168=x169.implies(x171);
		Formula x218=TRNop(x166, x162, x183);
		Formula x216=x169.not().implies(x218);
		Formula x167=x168.and(x216);
		Formula x164=x167.forAll(x166.oneOf(Process));
		Formula x160=x164.forAll(x162.oneOf(x121));
		Formula legaltrans = x160.and(x155);
		
		Formula res = Formula.compose(FormulaOperator.AND, decls, transifpossible, legaltrans);
		
		if (var == Variant.V1)
			return res.and(successfulRun());
		else if (var == Variant.V2)
			return res.and(traceWithoutLoop());
		else
			return res.and(badLivenessTrace());
		
	}

	private Formula equivStates(Expression s, Expression s1) {
		Expression x109=s.join(level);
		Expression x110=s1.join(level);
		Formula x108=x109.eq(x110);
		Expression x112=s.join(parent);
		Expression x113=s1.join(parent);
		Formula x111=x112.eq(x113);
		return x108.and(x111);
	}
			
	private Formula traceWithoutLoop() {
		Variable x101=Variable.unary("TraceWithoutLoop_s");
		Variable x103=Variable.unary("TraceWithoutLoop_s'");
		Formula x105=x101.eq(x103).not();

		Formula x109=equivStates(x101, x103).not();
		
		Formula x120=x103.in(x101.join(state_next.closure()));
		Formula x123=x103.eq(x101.join(state_next)).not();
		Formula x118=x120.and(x123);
		Variable x129=Variable.unary("PossTrans_p");

		Formula x130=TRAct(x129, x101, x103).or(TRNop(x129, x101, x103));
		
		Formula x127=x130.forAll(x129.oneOf(Process_rem.union(Root)));
		Formula x126=x127.not();
		Formula x117=x118.implies(x126);
		
		Formula x108=x109.and(x117);
		Formula x104=x105.implies(x108);
		Formula x98=x104.forAll(x101.oneOf(State).and(x103.oneOf(State)));
		
		Variable x176=Variable.unary("TraceWithoutLoop_s");
		Formula x178=spanTreeAtState(x176);
		Formula x177=x178.not();
		Formula x174=x177.forAll(x176.oneOf(State));
		return x98.and(x174);
	}
	
	private Formula badLivenessTrace() {

		Variable x101=Variable.unary("BadLivenessTrace_s");
		Variable x103=Variable.unary("BadLivenessTrace_s'");
		Formula x105=x101.eq(x103).not();
		Formula x104=x105.and(equivStates(x101, x103));
		Formula x98=x104.forSome(x101.oneOf(State).and(x103.oneOf(State)));
		
		Variable x116=Variable.unary("BadLivenessTrace_s");
		Formula x118=spanTreeAtState(x116);
		Formula x117=x118.not();
		Formula x114=x117.forAll(x116.oneOf(State));

		return x98.and(x114);
	}
	
	private Formula closure() {
		Variable x101=Variable.unary("Closure_s");
		Expression x102=State.difference(state_last);

		Formula x107=spanTreeAtState(x101);
		Expression x134=x101.join(parent);
		Expression x136=x101.join(state_next);
		Expression x135=x136.join(parent);
		Formula x133=x134.eq(x135);
		Formula x105=x107.implies(x133);
		Formula x99=x105.forAll(x101.oneOf(x102));
		return x99.not();
	}
	
	/**
	 * Returns a bounds for the given number of persons.
	 * 
	 * @return a bounds for the given number of persons.
	 */
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet pb = f.range(f.tuple("Root"), f.tuple("Process"+ (n_ps-1)));
		final TupleSet rb = f.range(f.tuple("Process1"), f.tuple("Process"+ (n_ps-1)));
		final TupleSet lb = f.range(f.tuple("Lvl0"), f.tuple("Lvl"+ (n_ps-1)));

		b.boundExactly(Root, f.setOf("Root"));
		b.boundExactly(Process_rem, rb);
		b.boundExactly(Level, lb);
		b.bound(adjacent, pb.product(pb));

		b.bound(level_first, lb);
		b.bound(level_next, lb.product(lb));
		b.bound(level_last, lb);

		return b;
	}

	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final TupleSet pb = f.range(f.tuple("Root"), f.tuple("Process"+ (n_ps-1)));
		final TupleSet lb = f.range(f.tuple("Lvl0"), f.tuple("Lvl"+ (n_ps-1)));
		final TupleSet sb = f.range(f.tuple("State0"), f.tuple("State"+ (n_ts-1)));

		b.boundExactly(State, sb);
		b.bound(runs, sb.product(pb));
		b.bound(level, sb.product(pb).product(lb));
		b.bound(parent, sb.product(pb).product(pb));

		b.bound(state_first, sb);
		b.bound(state_next, sb.product(sb));
		b.bound(state_last, sb);

		return b;
	}
	

	@Override
	public int getBitwidth() {
		return 1;
	}


	public String toString() {
		StringBuilder sb = new StringBuilder("Span");
		sb.append("-");
		sb.append(n_ps);		
		sb.append("-");
		sb.append(n_ts);		
		return sb.toString();
	}


	@Override
	public String shortName() {
		return "Span "+n_ps+" "+n_ts+" "+var.name();
	}
}
