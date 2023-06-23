/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.examples.pardinus.temporal;

import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class RingT extends DModel {

	public enum Variant1 {
		BADLIVENESS, GOODLIVENESS, GOODSAFETY;
	}

	public enum Variant2 {
		STATIC, VARIABLE;
	}

	// model parameters
	// number of processes and time instants
	private final int n_ps;
	// whether to check liveness property or safety, to enforce loopless
	// paths and assume variable processes
	private final Variant1 variant;
	private final Variant2 variable;

	// partition 1 relations
	private Relation pfirst, plast, pord, Process, succ, id, Id;
	// partition 2 relations
	private Relation toSend, elected;

	private Universe u;
	
	public RingT(String args[]) {
		this.n_ps = Integer.valueOf(args[0]);
		this.variant = Variant1.valueOf(args[1]);
		this.variable = Variant2.valueOf(args[2]);

		Process = Relation.unary("Process");
		succ = Relation.binary("succ");
		pfirst = Relation.unary("pfirst");
		plast = Relation.unary("plast");
		pord = Relation.binary("pord");

		id = Relation.binary("id_");
		Id = Relation.unary("Id");

		toSend = Relation.binary_variable("toSend");
		elected = Relation.unary_variable("elected");
	}

	/**
	 * Returns the declaration constraints.
	 * 
	 * @return <pre>
	 * sig Time {}
	 * sig Process {
	 *  toSend: Process -> Time,
	 *  elected: set Time }
	 * </pre>
	 */
	public Formula declarations() {
		final Formula electedDomRange = elected.in(Process).always();/*
																	 * TEMPORAL
																	 * OP
																	 */
		final Formula sendDomRange;
		if (variable == Variant2.VARIABLE)
			sendDomRange = toSend.in(Process.product(Id)).always();/*
																	 * TEMPORAL
																	 * OP
																	 */
		else
			sendDomRange = toSend.in(Process.product(Process)).always();/*
																		 * TEMPORAL
																		 * OP
																		 */
		return Formula.and(electedDomRange, sendDomRange);
	}

	/**
	 * Returns the init predicate.
	 * 
	 * @return <pre>
	 * pred init (t: Time) {all p: Process | p.toSend.t = p}
	 * </pre>
	 */
	public Formula init() {
		final Variable p = Variable.unary("p");
		final Formula f;
		if (variable == Variant2.VARIABLE)
			f = p.join(toSend).eq(p.join(id)).forAll(p.oneOf(Process));
		else
			f = p.join(toSend).eq(p).forAll(p.oneOf(Process));
		return f;
	}

	/**
	 * Returns the step predicate.
	 * 
	 * @return <pre>
	 * pred step (t, t�: Time, p: Process) {
	 *  let from = p.toSend, to = p.succ.toSend |
	 *   some id: p.toSend.t {
	 *    p.toSend.t� = p.toSend.t - id
	 *    p.succ.toSend .t� = p.succ.toSend .t + (id - PO/prevs(p.succ)) } }
	 * </pre>
	 */
	public Formula step(Expression p) {
		final Expression from = p.join(toSend);
		final Expression to = p.join(succ).join(toSend);

		final Expression fromPost = p.join(toSend.prime());/* TEMPORAL OP */
		final Expression toPost = p.join(succ).join(toSend.prime());/*
																	 * TEMPORAL
																	 * OP
																	 */

		final Variable idv = Variable.unary("id");
		final Expression prevs;

		if (variable == Variant2.VARIABLE)
			prevs = (p.join(succ).join(id)).join((pord.transpose()).closure());
		else
			prevs = (p.join(succ)).join((pord.transpose()).closure());

		final Formula f1 = fromPost.eq(from.difference(idv));
		final Formula f2 = toPost.eq(to.union(idv.difference(prevs)));
		return f1.and(f2).forSome(idv.oneOf(from));
	}

	/**
	 * Returns the skip predicate
	 * 
	 * @return <pre>pred skip (t, t�: Time, p: Process) {p.toSend.t = p.toSend.t�}
	 * 
	 *         <pre>
	 */
	public Formula skip(Expression p) {
		return p.join(toSend).eq(p.join(toSend.prime()));
	}/* TEMPORAL OP */

	/**
	 * Returns the Traces fact.
	 * 
	 * @return <pre>
	 * fact Traces {
	 *  init (TO/first ())
	 *  all t: Time - TO/last() | let t� = TO/next (t) |
	 *   all p: Process | step (t, t�, p) or step (t, t�, succ.p) or skip (t, t�, p) }
	 * </pre>
	 */
	public Formula traces() {
		final Variable p = Variable.unary("p");
		final Formula f = step(p).or(step(succ.join(p))).or(skip(p));
		final Formula fAll = f.forAll(p.oneOf(Process));
		return init().and(fAll.always());/* TEMPORAL OP */
	}

	/**
	 *
	 * Return DefineElected fact.
	 * 
	 * @return <pre>
	 * fact DefineElected {
	 *  no elected.TO/first()
	 *  all t: Time - TO/first()|
	 *   elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
	 * </pre>
	 */
	public Formula defineElected() {
		final Formula f1 = elected.no();
		final Variable p = Variable.unary("p");
		final Formula c;

		if (variable == Variant2.VARIABLE)
			// c =
			// (p.join(id)).in(p.join(toSend).join(t).difference(p.join(toSend).join(t.join(tord.transpose()))));
			// {p: Process | (after { p.id in p.toSend }) and p.id not in
			// p.toSend} }
			c = (p.join(id)).in(p.join(toSend)).after().and(p.join(id).in(p.join(toSend)).not());/*
																								 * TEMPORAL
																								 * OP
																								 */
		else
			// c =
			// p.in(p.join(toSend).join(t).difference(p.join(toSend).join(t.join(tord.transpose()))));
			c = p.in(p.join(toSend)).after().and((p.in(p.join(toSend))).not());/*
																			 * TEMPORAL
																			 * OP
																			 */

		final Expression comprehension = c.comprehension(p.oneOf(Process));
		final Formula f2 = elected.prime().eq(comprehension).always();/*
																	 * TEMPORAL
																	 * OP
																	 */
		return f1.and(f2);
	}

	/**
	 * Returns the progress predicate.
	 * 
	 * @return <pre>
	 * pred progress () {
	 *  all t: Time - TO/last() | let t� = TO/next (t) |
	 *   some Process.toSend.t => some p: Process | not skip (t, t�, p) }
	 * </pre>
	 */

	/*
	 * pred Progress { always {some Process.toSend => after { some p: Process |
	 * not skip [p]} } }
	 */

	public Formula progress() {
		final Variable p = Variable.unary("p");
		final Formula f1 = (Process.join(toSend).some()).implies(skip(p).not().forSome(p.oneOf(Process)));
		return f1.always();/* TEMPORAL OP */
	}

	/**
	 * Returns the AtLeastOneElected assertion.
	 * 
	 * @return <pre>
	 * assert AtLeastOneElected { progress () => some elected.Time }
	 * </pre>
	 */
	public Formula atLeastOneElectedLoop() {// GOODLIVENESS
		return (Process.some().and(progress())).implies(elected.some().eventually());/*
																					 * TEMPORAL
																					 * OP
																					 */
	}

	public Formula atLeastOneElected() { // //BADLIVENESS
		return (Process.some()).implies(elected.some().eventually());/*
																	 * TEMPORAL
																	 * OP
																	 */
	}

	/**
	 * Returns the atMostOneElected assertion
	 * 
	 * @return <pre>
	 * assert AtMostOneElected {lone elected.Time}
	 * </pre>
	 */
	public Formula atMostOneElected() { // GOODSAFETY
		return elected.lone().always();/* TEMPORAL OP */
	}

	/**
	 * Returns the declarations and facts of the model
	 * 
	 * @return the declarations and facts of the model
	 */
	public Formula invariants() {
		return declarations().and(traces()).and(defineElected());
	}

	/**
	 * Returns the conjunction of the invariants and the negation of
	 * atMostOneElected.
	 * 
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

	public Formula variableConstraints() {
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

	public Formula finalFormula() {
		if (!(variant == Variant1.GOODSAFETY))
			if (variant == Variant1.GOODLIVENESS)
				return (checkAtLeastOneElectedLoop());
			else
				return (checkAtLeastOneElected());
		else
			return (checkAtMostOneElected());
	}

	public PardinusBounds bounds1() {

		final List<String> atoms = new ArrayList<String>(n_ps);

		// add the process atoms
		for (int i = 0; i < n_ps; i++)
			atoms.add("Process" + i);

		// if variable processes, must consider Ids as a workaround to
		// totalorder
		if (variable == Variant2.VARIABLE) {
			for (int i = 0; i < n_ps; i++)
				atoms.add("Id" + i);
		}

		u = new Universe(atoms);
		final TupleFactory f = u.factory();

		final PardinusBounds b = new PardinusBounds(u);

		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (n_ps - 1)));

		b.bound(Process, pb);
		b.bound(succ, pb.product(pb));

		if (variable == Variant2.VARIABLE) {
			final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id" + (n_ps - 1)));
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

		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (n_ps - 1)));

		if (variable == Variant2.VARIABLE) {
			final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id" + (n_ps - 1)));
			b.bound(toSend, pb.product(ib));
		} else {
			b.bound(toSend, pb.product(pb));
		}
		b.bound(elected, pb);

		return b;
	}

	@Override
	public Formula partition1() {
		return variableConstraints();
	}

	@Override
	public Formula partition2() {
		return finalFormula();
	}

	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	public static void main(String[] args) {
		RingT model = new RingT(new String[] { "3", "BADLIVENESS", "STATIC" });

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.Glucose);
		opt.setMaxTraceLength(10);
		Solver solver = new Solver(opt);

		PardinusBounds bnds = model.bounds1();
		bnds.merge(model.bounds2());
		Solution sol = solver.solve(model.partition1().and(model.partition2()), bnds);

		System.out.println(sol);
		return;
	}
}
