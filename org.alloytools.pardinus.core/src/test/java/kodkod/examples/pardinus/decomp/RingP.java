package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * KodKod encoding of the following leader election algorithm:
 * 
 * <pre>
 * module internal/ringElection 
 * open util/ordering[Time] as TO 
 * open util/ordering[Process] as PO
 * 
 * sig Time {} 
 * sig Process { 
 *  succ: Process, 
 *  toSend: Process -> Time, 
 *  elected: set Time }
 * 
 * fact Ring {all p: Process | Process in p.^succ}
 * 
 * pred init (t: Time) {all p: Process | p.toSend.t = p}
 * 
 * pred step (t, t�: Time, p: Process) { 
 *  let from = p.toSend, to = p.succ.toSend |
 *   some id: from.t { 
 *    from.t� = from.t - id 
 *    to.t� = to.t + (id - PO/prevs(p.succ)) } }
 * 
 * pred skip (t, t�: Time, p: Process) {p.toSend.t = p.toSend.t�}
 * 
 * fact Traces { 
 *  init (TO/first ()) 
 *  all t: Time - TO/last() | let t� = TO/next (t) | 
 *   all p: Process | step (t, t�, p) or step (t, t�, succ.p) or skip (t, t�, p) }
 * 
 * fact DefineElected { 
 *  no elected.TO/first() 
 *  all t: Time - TO/first()|
 *   elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
 * 
 * 
 * pred progress () { 
 *  all t: Time - TO/last() | let t� = TO/next (t) | 
 *   some Process.toSend.t => some p: Process | not skip (t, t�, p) }
 * 
 * assert AtLeastOneElected { progress () => some elected.Time }
 * 
 * pred looplessPath () {no disj t, t�: Time | toSend.t = toSend.t�}
 * 
 * assert AtMostOneElected {lone elected.Time}
 * 
 * check AtMostOneElected for 3 Process, 7 Time 
 * run looplessPath for 13 Time, 3 Process
 * </pre>
 * @author Emina Torlak
 */
public final class RingP extends DModel {

	public enum Variant1 {
		BADLIVENESS,
		GOODLIVENESS,
		GOODSAFETY;
	}

	public enum Variant2 {
		STATIC,
		VARIABLE;
	}

	// model parameters
	// number of processes and time instants
	private final int n_ps, n_ts;
	// whether to check liveness property or safety, to enforce loopless 
	// paths and assume variable processes
	private final Variant1 variant;
	private final Variant2 variable; 
	

	// partition 1 relations
	private Relation pfirst, plast, pord, Process, succ, id, Id;
	// partition 2 relations
	private Relation tfirst, tlast, tord, Time, toSend, elected;

	// universe of atoms
	private final Universe u;
	
	/**
	 * Constructs an instance of the RingElection example.
	 */
	public RingP(String[] args) {
		this.n_ps = Integer.valueOf(args[0]);
		this.n_ts = Integer.valueOf(args[1]);
		this.variant = RingP.Variant1.valueOf(args[2]);
		this.variable = RingP.Variant2.valueOf(args[3]);
		
		Process = Relation.unary("Process");
		Time = Relation.unary("Time");
		succ = Relation.binary("succ");
		toSend = Relation.ternary("toSend");
		elected = Relation.binary("elected");
		pfirst = Relation.unary("pfirst");
		plast = Relation.unary("plast");
		pord = Relation.binary("pord");
		tfirst = Relation.unary("tfirst");
		tlast = Relation.unary("tlast");
		tord = Relation.binary("tord");

		final List<String> atoms = new ArrayList<String>(n_ps + n_ts);

		// add the process atoms
		for(int i = 0; i < n_ps; i++) 
			atoms.add("Process"+i);

		// add the time atoms
		for(int i = 0; i < n_ts; i++) 
			atoms.add("Time"+i);

		// if variable processes, must consider Ids as a workaround to totalorder
		if (variable == Variant2.VARIABLE) {
			id = Relation.binary("id");
			Id = Relation.unary("Id");
			for(int i = 0; i < n_ps; i++) 
				atoms.add("Id"+i);
		}
		
		u = new Universe(atoms);
	}
	
	/**
	 * Returns the declaration constraints.
	 * @return <pre>
	 * sig Time {} 
	 * sig Process { 
	 *  toSend: Process -> Time, 
	 *  elected: set Time }
	 * </pre> 
	 */
	public Formula declarations() {
		final Formula ordTime = tord.totalOrder(Time, tfirst, tlast);
		final Formula electedDomRange = elected.in(Process.product(Time));
		final Formula sendDomRange;
		if (variable == Variant2.VARIABLE) sendDomRange = toSend.in(Process.product(Id).product(Time));
		else sendDomRange = toSend.in(Process.product(Process).product(Time));
		return Formula.and(ordTime, electedDomRange, sendDomRange);
	}
	
	/**
	 * Returns the init predicate.
	 * @return <pre> pred init (t: Time) {all p: Process | p.toSend.t = p} </pre>
	 */
	public Formula init(Expression t) {
		final Variable p = Variable.unary("p");
		final Formula f;
		if (variable == Variant2.VARIABLE) f = p.join(toSend).join(t).eq(p.join(id)).forAll(p.oneOf(Process));
		else f = p.join(toSend).join(t).eq(p).forAll(p.oneOf(Process));
		return f;
	}
	
	/**
	 * Returns the step predicate.
	 * @return
	 * <pre>
	 * pred step (t, t�: Time, p: Process) { 
	 *  let from = p.toSend, to = p.succ.toSend |
	 *   some id: p.toSend.t { 
	 *    p.toSend.t� = p.toSend.t - id 
	 *    p.succ.toSend .t� = p.succ.toSend .t + (id - PO/prevs(p.succ)) } }
	 * </pre>  
	 */
	public Formula step(Expression t1, Expression t2, Expression p) {
		final Expression from = p.join(toSend);
		final Expression to = p.join(succ).join(toSend);
		final Variable idv = Variable.unary("id");
		final Expression prevs;
		
		if (variable == Variant2.VARIABLE)
			prevs = (p.join(succ).join(id)).join((pord.transpose()).closure());
		else
			prevs = (p.join(succ)).join((pord.transpose()).closure());

		final Formula f1 = from.join(t2).eq(from.join(t1).difference(idv));
		final Formula f2 = to.join(t2).eq(to.join(t1).union(idv.difference(prevs)));
		return f1.and(f2).forSome(idv.oneOf(from.join(t1)));
	}
	
	
	/**
	 * Returns the skip predicate
	 * @return <pre>pred skip (t, t�: Time, p: Process) {p.toSend.t = p.toSend.t�}<pre>
	 */
	public Formula skip(Expression t1, Expression t2, Expression p) {
		return p.join(toSend).join(t1).eq(p.join(toSend).join(t2));
	}
	
	/**
	 * Returns the Traces fact.
	 * @return <pre>
	 * fact Traces { 
	 *  init (TO/first ()) 
	 *  all t: Time - TO/last() | let t� = TO/next (t) | 
	 *   all p: Process | step (t, t�, p) or step (t, t�, succ.p) or skip (t, t�, p) }
	 *  </pre>
	 */
	public Formula traces() {
		final Variable t1 = Variable.unary("t");
		final Expression t2 = t1.join(tord);
		final Variable p = Variable.unary("p");
		final Formula f = step(t1, t2, p).or(step(t1, t2, succ.join(p))).or(skip(t1, t2, p));
		final Formula fAll = f.forAll(p.oneOf(Process)).forAll(t1.oneOf(Time.difference(tlast)));
		return init(tfirst).and(fAll);
	}
	
	/**
	 * Return DefineElected fact.
	 * @return <pre>
	 * fact DefineElected { 
	 *  no elected.TO/first() 
	 *  all t: Time - TO/first()|
	 *   elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
	 * </pre>
	 */
	public Formula defineElected() {
		final Variable t = Variable.unary("t");
		final Formula f1 = elected.join(tfirst).no();
		final Variable p = Variable.unary("p");
		final Formula c;
		
		if (variable == Variant2.VARIABLE)
			c = (p.join(id)).in(p.join(toSend).join(t).difference(p.join(toSend).join(t.join(tord.transpose()))));
		else
			c = p.in(p.join(toSend).join(t).difference(p.join(toSend).join(t.join(tord.transpose()))));

		final Expression comprehension = c.comprehension(p.oneOf(Process));
		final Formula f2 = elected.join(t).eq(comprehension).forAll(t.oneOf(Time.difference(tfirst)));
		return f1.and(f2);
	}
	
	/**
	 * Returns the progress predicate.
	 * @return <pre>
	 * pred progress () { 
	 *  all t: Time - TO/last() | let t� = TO/next (t) | 
	 *   some Process.toSend.t => some p: Process | not skip (t, t�, p) }
	 * </pre>  
	 */
	public Formula progress() {
		final Variable t1 = Variable.unary("t");
		final Expression t2 = t1.join(tord);
		final Variable p = Variable.unary("p");
		final Formula f1 = Process.join(toSend).join(t1).some().implies(skip(t1, t2, p).not().forSome(p.oneOf(Process)));
		return f1.forAll(t1.oneOf(Time.difference(tlast)));
	}
	
	/**
	 * Returns the looplessPath predicate
	 * @return <pre>pred looplessPath () {no disj t, t�: Time | toSend.t = toSend.t�}</pre>
	 */
	public Formula looplessPath() {
		final Variable t1 = Variable.unary("t");
		final Variable t2 = Variable.unary("t'");
		// all t, t': Time | some t&t' || !(toSend.t = toSend.t�)
		final Formula f1 = t1.intersection(t2).some().or(toSend.join(t1).eq(toSend.join(t2)).not());
		return f1.forAll(t1.oneOf(Time).and(t2.oneOf(Time)));
	}
	
	/**
	 * Returns the AtLeastOneElected assertion.
	 * @return <pre>assert AtLeastOneElected { progress () => some elected.Time }</pre>
	 */
	public Formula atLeastOneElectedLoop() {
		return (progress().and(looplessPath().not())).implies(elected.join(Time).some());
	}

	public Formula atLeastOneElected() {
		return progress().implies(elected.join(Time).some());
	}

	/**
	 * Returns the atMostOneElected assertion
	 * @return <pre>assert AtMostOneElected {lone elected.Time}</pre>
	 */
	public Formula atMostOneElected() {
		return elected.join(Time).lone();
	}
	
	/**
	 * Returns the declarations and facts of the model
	 * @return the declarations and facts of the model
	 */
	public Formula invariants() {
		return declarations().and(traces()).and(defineElected());
	}
	
	
	/**
	 * Returns the conjunction of the invariants and the negation of atMostOneElected.
	 * @return invariants() && !atMostOneElected()
	 */
	public Formula checkAtMostOneElected() {
		return invariants().and(atMostOneElected().not());
	}

	public Formula checkAtLeastOneElected() {
		return invariants().and(atLeastOneElected().not());
	}
	
	public Formula checkAtLeastOneElectedLoop() {
		return invariants().and(atLeastOneElectedLoop().not());
	}

	/**
	 * Returns a bounds object that scopes Process, Time, and their
	 * fields according to given values.
	 * @return bounds
	 */
	public PardinusBounds bounds1() {

		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process"+ (n_ps-1)));
		
		b.bound(Process, pb);
		b.bound(succ, pb.product(pb));
		
		if (variable == Variant2.VARIABLE) {
			final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id"+ (n_ps-1)));
			b.bound(Id, ib);
			b.bound(id, pb.product(ib));
			b.bound(pfirst, ib);
			b.bound(plast, ib);
			b.bound(pord, ib.product(ib));
		} else {
			b.bound(pfirst, pb);
			b.bound(plast, pb);
			b.bound(pord, pb.product(pb));
		}
				
		return b;
	}
	
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process"+ (n_ps-1)));
		final TupleSet tb = f.range(f.tuple("Time0"), f.tuple("Time"+(n_ts-1)));
		
		if (variable == Variant2.VARIABLE) {
			final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id"+ (n_ps-1)));
			b.bound(toSend, pb.product(ib).product(tb));
		}
		else			
			b.bound(toSend, pb.product(pb).product(tb));
		
		b.bound(elected, pb.product(tb));
		
		b.bound(Time, tb);
		b.bound(tord, tb.product(tb));
		b.bound(tfirst, tb);
		b.bound(tlast, tb);
		
		return b;
	}
	
	/**
	 * Returns the declaration constraints.
	 * @return <pre>
	 * sig Process { 
	 *  succ: Process }
	 * </pre> 
	 * 
	 * Returns the fact Ring.
	 * @return <pre>fact Ring {all p: Process | Process in p.^succ}</pre>
	 */
	public Formula partition1() {
		final Formula ordProcess;
		if (variable == Variant2.VARIABLE) {
			final Formula f0 = id.function(Process, Id);
			final Formula f1 = Process.some();
			final Variable p1 = Variable.unary("p");
			final Formula f2 = (id.join(p1).lone()).forAll(p1.oneOf(Id));
			ordProcess = f2.and(f1).and(f0).and(pord.totalOrder(Id, pfirst, plast));
		} else
			ordProcess = pord.totalOrder(Process, pfirst, plast);
		
		final Formula succFunction = succ.function(Process, Process);

		final Variable p = Variable.unary("p");
		final Formula ring = Process.in(p.join(succ.closure())).forAll(p.oneOf(Process));

		return Formula.and(ordProcess, succFunction, ring);
	}

	
	public Formula partition2() {
		if (!(variant == Variant1.GOODSAFETY))
			if (variant == Variant1.GOODLIVENESS) return checkAtLeastOneElectedLoop();
			else return checkAtLeastOneElected();
		else return checkAtMostOneElected();
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	@Override
	public String shortName() {
		return "Ring "+n_ps+" "+n_ts+" "+variant.name()+" "+variable.name();
	}
	
}
