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
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.temporal.RingT.Variant2;
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
public class RingT2 extends DModel {

	public enum Variant1 {
		BADLIVENESS, GOODLIVENESS, GOODSAFETY, SCENARIO;
	}

	// model parameters
	// number of processes and time instants
	private final int n_ps;
	// whether to check liveness property or safety, to enforce loopless
	// paths and assume variable processes
	private final Variant1 variant;

	// partition 1 relations
	private Relation next, Process, succ, id, Id;
	// partition 2 relations
	private Relation outbox, Elected;

	private Universe u;
	
	public RingT2(String args[]) {
		this.n_ps = Integer.valueOf(args[0]);
		this.variant = Variant1.valueOf(args[1]);

		Process = Relation.unary("Process");
		succ = Relation.binary("succ");
		next = Relation.binary("next");

		id = Relation.binary("id");
		Id = Relation.unary("Id");

		outbox = Relation.binary_variable("outbox");
		Elected = Relation.unary_variable("Elected");
	}


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
		final Formula f0 = outbox.eq(id);

		final Variable p = Variable.unary("p");
		final Variable i = Variable.unary("i");

		
		final Expression currs = (outbox.difference(p.product(i)));
		final Expression prevs = p.join(succ).product(i.difference((next.closure()).join(p.join(succ.join(id)))));

		final Formula f1 = ((outbox.prime()).eq(currs.union(prevs))).forSome(i.oneOf(p.join(outbox))).forSome(p.oneOf(Process)).always();
		
		return f0.and(f1);
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
		final Variable p = Variable.unary("p");
		final Formula f =((p.join(id).in(p.join(outbox))).and((p.join(id).in(p.join(outbox)).not().before()))).once();
		final Expression e = f.comprehension(p.oneOf(Process));
		return Elected.eq(e).always();
	}

	public Formula defineElectedFixed() {
		final Variable p = Variable.unary("p");
		Formula f = ((p.join(id).in(p.join(outbox))).and((p.join(id).in(p.join(outbox)).not().before()))).once();
		f = f.or(p.join(succ).eq(p));
		final Expression e = f.comprehension(p.oneOf(Process));
		return Elected.eq(e).always();
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

	/**
	 * Returns the AtLeastOneElected assertion.
	 * 
	 * @return <pre>
	 * assert AtLeastOneElected { progress () => some elected.Time }
	 * </pre>
	 */
	public Formula atLeastOneElected() {// GOODLIVENESS
		return Elected.some().eventually();/*
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
		final Variable p = Variable.unary("p");
		return (Elected.in(p).always()).forAll(p.oneOf(Elected)).always();
	}

	/**
	 * Returns the declarations and facts of the model
	 * 
	 * @return the declarations and facts of the model
	 */
	public Formula invariants() {
		return traces().and(defineElected())/*.and(declarations())*/; // remove decls with symb bounds
	}
	
	public Formula declarations() {
		final Formula f1 = Elected.in(Process).always();
		final Formula f2 = outbox.in(Process.product(Id)).always();														 
		return Formula.and(f1, f2);
	}

	/**
	 * Returns the declarations and facts of the model
	 * 
	 * @return the declarations and facts of the model
	 */
	public Formula invariantsFixed() {
		return traces().and(defineElectedFixed())/*.and(declarations())*/; // remove decls with symb bounds
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

	public Formula checkAtLeastOneElectedFixed() {
		return invariantsFixed().and(atLeastOneElected().not());
	}

	public Formula runSomeElected() {
		return invariants().and(atLeastOneElected());
	}

	public Formula variableConstraints() {
		final Variable p = Variable.unary("p");
		final Formula f1 = (p.join(id).one()).forAll(p.oneOf(Process));
		final Variable i = Variable.unary("i");
		final Formula f2 = (id.join(i).lone()).forAll(i.oneOf(Id));
		final Formula f3 = (p.join(succ).one()).forAll(p.oneOf(Process));
		final Formula f4 = (Process.in(p.join(succ.closure()))).forAll(p.oneOf(Process));
		return Formula.and(f1,f2,f3,f4);
	}

	public Formula finalFormula() {
		switch (variant) {
		case BADLIVENESS:
			return checkAtLeastOneElected();
		case GOODLIVENESS:
			return checkAtLeastOneElectedFixed();
		case GOODSAFETY:
			return checkAtMostOneElected();
		default:
			return runSomeElected();
		}
	}

	public PardinusBounds bounds1() {

		final List<String> atoms = new ArrayList<String>(n_ps);

		// add the process and id atoms
		for (int i = 0; i < n_ps; i++) 
			atoms.add("Process" + i);
		for (int i = 0; i < n_ps; i++) 
			atoms.add("Id" + i);

		u = new Universe(atoms);
		final TupleFactory f = u.factory();

		final PardinusBounds b = new PardinusBounds(u);

		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (n_ps - 1)));
		final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id" + (n_ps - 1)));
		final TupleSet nb = f.noneOf(2);

		for (int i = 0; i < n_ps - 1; i++) {
			nb.add(f.tuple("Id"+i).product(f.tuple("Id"+(i+1))));
		}
		
		b.boundExactly(Id, ib);
		b.boundExactly(next, nb);

		b.bound(Process, pb);
		b.bound(id, Process.product(Id));
		b.bound(succ, Process.product(Process));


		return b;
	}

	public Bounds bounds2() {

		final PardinusBounds b = new PardinusBounds(u);

		final TupleFactory f = u.factory();
		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (n_ps - 1)));
		final TupleSet ib = f.range(f.tuple("Id0"), f.tuple("Id" + (n_ps - 1)));
		
		b.bound(outbox, Process.product(Id));
		b.bound(Elected, Process);

		// switch with former for symb bounds
//		b.bound(outbox, pb.product(ib));
//		b.bound(Elected, pb);

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
		RingT2 model = new RingT2(new String[] { "9", "GOODLIVENESS" });

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.Glucose);
		opt.setRunDecomposed(true);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setMaxTraceLength(10);
//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		PardinusSolver solver = new PardinusSolver(opt);

		PardinusBounds bnds = new PardinusBounds(model.bounds1(),model.bounds2());
		Formula f = model.partition1().and(model.partition2());
		Solution sol = solver.solve(f, bnds);

		System.out.println(sol);
		return;
	}
}
