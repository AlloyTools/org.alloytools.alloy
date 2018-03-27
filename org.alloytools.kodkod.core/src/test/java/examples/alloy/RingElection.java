package examples.alloy;

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
 * pred step (t, t': Time, p: Process) {
 *  let from = p.toSend, to = p.succ.toSend |
 *   some id: from.t {
 *    from.t' = from.t - id
 *    to.t' = to.t + (id - PO/prevs(p.succ)) } }
 *
 * pred skip (t, t': Time, p: Process) {p.toSend.t = p.toSend.t'}
 *
 * fact Traces {
 *  init (TO/first ())
 *  all t: Time - TO/last() | let t' = TO/next (t) |
 *   all p: Process | step (t, t', p) or step (t, t', succ.p) or skip (t, t', p) }
 *
 * fact DefineElected {
 *  no elected.TO/first()
 *  all t: Time - TO/first()|
 *   elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
 *
 *
 * pred progress () {
 *  all t: Time - TO/last() | let t' = TO/next (t) |
 *   some Process.toSend.t => some p: Process | not skip (t, t', p) }
 *
 * assert AtLeastOneElected { progress () => some elected.Time }
 *
 * pred looplessPath () {no disj t, t': Time | toSend.t = toSend.t'}
 *
 * assert AtMostOneElected {lone elected.Time}
 *
 * check AtMostOneElected for 3 Process, 7 Time
 * run looplessPath for 13 Time, 3 Process
 * </pre>
 *
 * @author Emina Torlak
 */
public final class RingElection {

    private final Relation Process, Time, succ, toSend, elected;
    private final Relation pfirst, plast, pord, tfirst, tlast, tord;

    /**
     * Constructs an instance of the RingElection example.
     */
    public RingElection() {
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
    }

    /**
     * Returns the declaration constraints.
     *
     * @return
     *
     *         <pre>
     * sig Time {}
     * sig Process {
     *  succ: Process,
     *  toSend: Process -> Time,
     *  elected: set Time }
     *         </pre>
     */
    public Formula declarations() {
        final Formula ordTime = tord.totalOrder(Time, tfirst, tlast);
        final Formula ordProcess = pord.totalOrder(Process, pfirst, plast);
        final Formula succFunction = succ.function(Process, Process);
        final Formula electedDomRange = elected.in(Process.product(Time));
        return succFunction.and(ordTime).and(ordProcess).and(electedDomRange);
    }

    /**
     * Returns the fact Ring.
     *
     * @return
     *
     *         <pre>
     * fact Ring {all p: Process | Process in p.^succ}
     *         </pre>
     */
    public Formula ring() {
        final Variable p = Variable.unary("p");
        return Process.in(p.join(succ.closure())).forAll(p.oneOf(Process));
    }

    /**
     * Returns the init predicate.
     *
     * @return
     *
     *         <pre>
     *  pred init (t: Time) {all p: Process | p.toSend.t = p}
     *         </pre>
     */
    public Formula init(Expression t) {
        final Variable p = Variable.unary("p");
        return p.join(toSend).join(t).eq(p).forAll(p.oneOf(Process));
    }

    /**
     * Returns the step predicate.
     *
     * @return
     *
     *         <pre>
     * pred step (t, t': Time, p: Process) {
     *  let from = p.toSend, to = p.succ.toSend |
     *   some id: from.t {
     *    from.t' = from.t - id
     *    to.t' = to.t + (id - PO/prevs(p.succ)) } }
     *         </pre>
     */
    public Formula step(Expression t1, Expression t2, Expression p) {
        final Expression from = p.join(toSend);
        final Expression to = p.join(succ).join(toSend);
        final Variable id = Variable.unary("id");
        final Expression prevs = (p.join(succ)).join((pord.transpose()).closure());
        final Formula f1 = from.join(t2).eq(from.join(t1).difference(id));
        final Formula f2 = to.join(t2).eq(to.join(t1).union(id.difference(prevs)));
        return f1.and(f2).forSome(id.oneOf(from.join(t1)));
    }

    /**
     * Returns the skip predicate
     *
     * @return
     *
     *         <pre>
     *         pred skip (t, t': Time, p: Process) {p.toSend.t = p.toSend.t'}
     *
     *         <pre>
     */
    public Formula skip(Expression t1, Expression t2, Expression p) {
        return p.join(toSend).join(t1).eq(p.join(toSend).join(t2));
    }

    /**
     * Returns the Traces fact.
     *
     * @return
     *
     *         <pre>
     * fact Traces {
     *  init (TO/first ())
     *  all t: Time - TO/last() | let t' = TO/next (t) |
     *   all p: Process | step (t, t', p) or step (t, t', succ.p) or skip (t, t', p) }
     *         </pre>
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
     *
     * @return
     *
     *         <pre>
     * fact DefineElected {
     *  no elected.TO/first()
     *  all t: Time - TO/first()|
     *   elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
     *         </pre>
     */
    public Formula defineElected() {
        final Variable t = Variable.unary("t");
        final Formula f1 = elected.join(tfirst).no();
        final Variable p = Variable.unary("p");
        final Formula c = p.in(p.join(toSend).join(t).difference(p.join(toSend).join(t.join(tord.transpose()))));
        final Expression comprehension = c.comprehension(p.oneOf(Process));
        final Formula f2 = elected.join(t).eq(comprehension).forAll(t.oneOf(Time.difference(tfirst)));
        return f1.and(f2);
    }

    /**
     * Returns the progress predicate.
     *
     * @return
     *
     *         <pre>
     * pred progress () {
     *  all t: Time - TO/last() | let t' = TO/next (t) |
     *   some Process.toSend.t => some p: Process | not skip (t, t', p) }
     *         </pre>
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
     *
     * @return
     *
     *         <pre>
     * pred looplessPath () {no disj t, t': Time | toSend.t = toSend.t'}
     *         </pre>
     */
    public Formula looplessPath() {
        final Variable t1 = Variable.unary("t");
        final Variable t2 = Variable.unary("t'");
        // all t, t': Time | some t&t' || !(toSend.t = toSend.t')
        final Formula f1 = t1.intersection(t2).some().or(toSend.join(t1).eq(toSend.join(t2)).not());
        return f1.forAll(t1.oneOf(Time).and(t2.oneOf(Time)));
    }

    /**
     * Returns the AtLeastOneElected assertion.
     *
     * @return
     *
     *         <pre>
     * assert AtLeastOneElected { progress () => some elected.Time }
     *         </pre>
     */
    public Formula atLeastOneElected() {
        return progress().implies(elected.join(Time).some());
    }

    /**
     * Returns the atMostOneElected assertion
     *
     * @return
     *
     *         <pre>
     * assert AtMostOneElected {lone elected.Time}
     *         </pre>
     */
    public Formula atMostOneElected() {
        return elected.join(Time).lone();
    }

    /**
     * Returns the declarations and facts of the model
     *
     * @return the declarations and facts of the model
     */
    public Formula invariants() {
        return declarations().and(ring()).and(traces()).and(defineElected());
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

    /**
     * Returns a bounds object with scope processes and times.
     *
     * @return bounds object with scope processes and times.
     */
    public Bounds bounds(int scope) {
        return bounds(scope, scope);
    }

    /**
     * Returns a bounds object that scopes Process, Time, and their fields according
     * to given values.
     *
     * @return bounds
     */
    public Bounds bounds(int processes, int times) {
        final List<String> atoms = new ArrayList<String>(processes + times);
        for (int i = 0; i < processes; i++) {
            atoms.add("Process" + i);
        }
        for (int i = 0; i < times; i++) {
            atoms.add("Time" + i);
        }
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (processes - 1)));
        final TupleSet tb = f.range(f.tuple("Time0"), f.tuple("Time" + (times - 1)));

        b.bound(Process, pb);
        b.bound(succ, pb.product(pb));
        b.bound(toSend, pb.product(pb).product(tb));
        b.bound(elected, pb.product(tb));
        b.bound(pord, pb.product(pb));
        b.bound(pfirst, pb);
        b.bound(plast, pb);

        b.bound(Time, tb);
        b.bound(tord, tb.product(tb));
        b.bound(tfirst, tb);
        b.bound(tlast, tb);

        return b;
    }

    private static void usage() {
        System.out.println("java examples.RingElection [# processes] [# times]");
        System.exit(1);
    }

    /**
     * Usage: java examples.RingElection [# processes] [# times]
     */
    public static void main(String[] args) {
        if (args.length < 2)
            usage();

        try {
            final RingElection model = new RingElection();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);

            final int p = Integer.parseInt(args[0]);
            final int t = Integer.parseInt(args[1]);

            final Formula checkAtMostOneElected = model.checkAtMostOneElected();
            final Bounds boundspt = model.bounds(p, t);

            System.out.println("*****check AtMostOneElected for " + p + " Process, " + t + " Time*****");
            Solution sol1 = solver.solve(checkAtMostOneElected, boundspt);
            System.out.println(sol1);

            // // run looplessPath for 13 Time, 3 Process
            // final Formula runLooplessPath =
            // model.declsAndFacts();//.and(model.looplessPath());
            // final Bounds bounds313 = model.bounds(p, t);
            // System.out.println("*****run looplessPath for 13 Time, 3
            // Process*****");
            // System.out.println(runLooplessPath);
            // System.out.println(bounds313);
            // Solution sol2 = solver.solve(runLooplessPath, bounds313);
            // System.out.println(sol2);

        } catch (NumberFormatException nfe) {
            usage();
        }
    }

}
