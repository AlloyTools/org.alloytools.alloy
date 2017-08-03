package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Decls;
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
 * Kodkod encoding of models/examples/algorithms/dijkstra.als.
 * @author Emina Torlak
 */
public final class Dijkstra {

	private final Relation Process, Mutex, State, holds, waits;
	private final Relation sfirst, slast, sord, mfirst, mlast, mord;
	
	/**
	 * Creates an instance of Dijkstra example.
	 */
	public Dijkstra() {
		Process = Relation.unary("Process");
		Mutex = Relation.unary("Mutex");
		State = Relation.unary("State");
		holds = Relation.ternary("holds");
		waits = Relation.ternary("waits");
		sfirst = Relation.unary("sfirst");
		slast = Relation.unary("slast");
		sord = Relation.binary("sord");
		mfirst = Relation.unary("mfirst");
		mlast = Relation.unary("mlast");
		mord = Relation.binary("mord");
	}
	
	/**
	 * Returns the declaration constraints.
	 * @return 
	 * <pre>
	 * sig Process {} 
	 * sig Mutex {}
	 * sig State { holds, waits: Process -> Mutex }
	 * </pre>
	 */
	public Formula declarations() {
		final Formula f1 = sord.totalOrder(State, sfirst, slast);
		final Formula f2 = mord.totalOrder(Mutex, mfirst, mlast);
		final Formula f3 = holds.in(State.product(Process).product(Mutex));
		final Formula f4 = waits.in(State.product(Process).product(Mutex));
		return Formula.and(f1, f2, f3, f4);
	}
	
	/**
	 * Returns the initial predicate for state s.
	 * @return
	 * <pre>
	 * pred State.Initial () { no this.holds + this.waits }
	 * </pre>
	 */
	public Formula initial(Expression s) {
		return s.join(holds).union(s.join(waits)).no();
	}
	
	/**
	 * Returns the free predicate for state s and mutex m.
	 * @return 
	 * <pre>
	 * pred State.IsFree (m: Mutex) {
	 * // no process holds this mutex
	 * no m.~(this.holds)
	 * }
	 * </pre>
	 */
	public Formula isFree(Expression s, Expression m) {
		return m.join((s.join(holds)).transpose()).no();
	}
	
	/**
	 * Returns the isStalled predicate for state s and process p. 
	 * @return 
	 * <pre>
	 * pred State.IsStalled (p: Process) { some p.(this.waits) } 
	 * </pre>
	 */
	public Formula isStalled(Expression s, Expression p) {
		return p.join(s.join(waits)).some();
	}
	
	/**
	 * Returns the GrabMutex predicate for states s1, s2, process p and mutex m. 
	 * @return 
	 * <pre>
	 * pred State.GrabMutex (p: Process, m: Mutex, s': State) {
	 *  // a process can only act if it is not 
	 *  // waiting for a mutex
	 * !this::IsStalled(p)
	 * // can only grab a mutex we do not yet hold
	 * 	m !in p.(this.holds)
	 * this::IsFree (m) => {
	 *    // if the mutex is free, we now hold it,
	 *    // and do not become stalled
	 *    p.(s'.holds) = p.(this.holds) + m
	 *    no p.(s'.waits)
	 *  } else {
	 *   // if the mutex was not free,
	 *   // we still hold the same mutexes we held,
	 *   // and are now waiting on the mutex
	 *   // that we tried to grab.
	 *   p.(s'.holds) = p.(this.holds)
	 *   p.(s'.waits) = m
	 * }
	 * all otherProc: Process - p | {
	 *    otherProc.(s'.holds) = otherProc.(this.holds)
	 *    otherProc.(s'.waits) = otherProc.(this.waits)
	 * }
	 * }
	 * </pre>
	 */
	public Formula grabMutex(Expression s1, Expression s2, Expression p, Expression m) {
		final Formula f1 = isStalled(s1,p).not().and(m.in(p.join(s1.join(holds))).not());
		final Formula isFree = isFree(s1,m);
		final Formula f2 = p.join(s2.join(holds)).eq(p.join(s1.join(holds)).union(m));
		final Formula f3 = p.join(s2.join(waits)).no();
		final Formula f4 = isFree.implies(f2.and(f3));
		final Formula f5 = p.join(s2.join(holds)).eq(p.join(s1.join(holds)));
		final Formula f6 = p.join(s2.join(waits)).eq(m);
		final Formula f7 = isFree.not().implies(f5.and(f6));
		final Variable otherProc = Variable.unary("otherProc");
		final Formula f8 = otherProc.join(s2.join(holds)).eq(otherProc.join(s1.join(holds)));
		final Formula f9 = otherProc.join(s2.join(waits)).eq(otherProc.join(s1.join(waits)));
		final Formula f10 = f8.and(f9).forAll(otherProc.oneOf(Process.difference(p)));
		return Formula.and(f1, f4, f7, f10);
	}
	
	/**
	 * Returns the GrabMutex predicate for states s1, s2, process p and mutex m. 
	 * @return 
	 * <pre>
	 * pred State.ReleaseMutex (p: Process, m: Mutex, s': State) {
	 *   !this::IsStalled(p)
	 *   m in p.(this.holds)
	 *   p.(s'.holds) = p.(this.holds) - m
	 *   no p.(s'.waits)
	 *   no m.~(this.waits) => {
	 *       no m.~(s'.holds)
	 *       no m.~(s'.waits)
	 *    } else {
	 *       some lucky: m.~(this.waits) | {
	 *       m.~(s'.waits) = m.~(this.waits) - lucky
	 *     m.~(s'.holds) = lucky
	 *    }
	 *   }
	 *   all mu: Mutex - m {
	 *     mu.~(s'.waits) = mu.~(this.waits)
	 *     mu.~(s'.holds)= mu.~(this.holds)
	 *   }
	 * }
	 * </pre>
	 */
	public Formula releaseMutex(Expression s1, Expression s2, Expression p, Expression m) {
		final Formula f1 = isStalled(s1,p).not().and(m.in(p.join(s1.join(holds))));
		final Formula f2 = p.join(s2.join(holds)).eq(p.join(s1.join(holds)).difference(m));
		final Formula f3 = p.join(s2.join(waits)).no();
		final Expression cexpr = m.join((s1.join(waits)).transpose());
		final Formula f4 = m.join(s2.join(holds).transpose()).no();
		final Formula f5 = m.join(s2.join(waits).transpose()).no();
		final Formula f6 = cexpr.no().implies(f4.and(f5));
		final Variable lucky = Variable.unary("lucky");
		final Formula f7 = m.join(s2.join(waits).transpose()).eq(m.join(s1.join(waits).transpose()).difference(lucky));
		final Formula f8 = m.join(s2.join(holds).transpose()).eq(lucky);
		final Formula f9 = f7.and(f8).forSome(lucky.oneOf(m.join(s1.join(waits).transpose())));
		final Formula f10 = cexpr.some().implies(f9);
		final Variable mu = Variable.unary("mu");
		final Formula f11 = mu.join(s2.join(waits).transpose()).eq(mu.join(s1.join(waits).transpose()));
		final Formula f12 = mu.join(s2.join(holds).transpose()).eq(mu.join(s1.join(holds).transpose()));
		final Formula f13 = f11.and(f12).forAll(mu.oneOf(Mutex.difference(m)));
		return Formula.and(f1, f2, f3, f6, f10, f13);
	}
	
	/**
	 * Returns the GrabOrRelease predicate.
	 * @return 
	 * <pre>
	 * pred GrabOrRelease () {
	 *    Initial(so/first()) &&
	 *    (
	 *    all pre: State - so/last () | let post = so/next (pre) | 
	 *       (post.holds = pre.holds && post.waits = pre.waits)
	 *        ||
	 *       (some p: Process, m: Mutex | pre::GrabMutex (p, m, post))
	 *        ||
	 *       (some p: Process, m: Mutex | pre::ReleaseMutex (p, m, post))
	 *    
	 *    )
	 * }
	 * </pre>
	 */
	public Formula grabOrRelease() {
		final Variable pre = Variable.unary("pre");
		final Expression post = pre.join(sord);
		final Formula f1 = post.join(holds).eq(pre.join(holds));
		final Formula f2 = post.join(waits).eq(pre.join(waits));
		final Variable p = Variable.unary("p");
		final Variable m = Variable.unary("m");
		final Decls d = p.oneOf(Process).and(m.oneOf(Mutex));
		final Formula f3 = grabMutex(pre, post, p, m).forSome(d);
		final Formula f4 = releaseMutex(pre, post, p, m).forSome(d);
		return initial(sfirst).and(((f1.and(f2)).or(f3).or(f4)).forAll(pre.oneOf(State.difference(slast))));
	}
	
	/**
	 * Returns the Deadlock predicate.
	 * @return
	 * <pre> 
	 * pred Deadlock () {
     *  some s: State | all p: Process | some p.(s.waits)
     * }
     * </pre>
	 */
	public Formula deadlock() {
		final Variable s = Variable.unary("s");
		final Variable p = Variable.unary("p");
		return p.join(s.join(waits)).some().forAll(p.oneOf(Process)).forSome(s.oneOf(State));
	}
	
	/**
	 * Returns the GrabbedInOrder predicate.
	 * @return 
	 * <pre>
	 * pred GrabbedInOrder ( ) {
	 * all pre: State - so/last() |
	 *  let post = so/next(pre) |
	 *     let had = Process.(pre.holds), have = Process.(post.holds) |
	 *     let grabbed = have - had |
	 *        some grabbed => grabbed in mo/nexts(had)
	 * }
	 * </pre>
	 */
	public Formula grabbedInOrder() {
		final Variable pre = Variable.unary("pre");
		final Expression post = pre.join(sord);
		final Expression had = Process.join(pre.join(holds));
		final Expression have = Process.join(post.join(holds));
		final Expression grabbed = have.difference(had);
		return grabbed.some().implies(grabbed.in(had.join(mord.closure()))).forAll(pre.oneOf(State.difference(slast)));
	}
	
	/**
	 * Returns the DijkstraPreventsDeadlocks assertion.
	 * @return
	 * <pre> 
	 * assert DijkstraPreventsDeadlocks {
	 *  some Process && GrabOrRelease() && GrabbedInOrder() => ! Deadlock()
	 * }
	 * </pre>
	 */
	public Formula checkDijkstraPreventsDeadlocks() {
		return Formula.and(declarations(), Process.some(), grabOrRelease(), grabbedInOrder(), deadlock());
	}
	
	/**
	 * Returns the showDijkstra predicate.
	 * @return he showDijkstra predicate
	 */
	public Formula showDijkstra() {
		return declarations().and(grabOrRelease()).and(deadlock()).and(waits.some());
	}
	
	/**
	 * Returns the bounds that allocate the given number of atoms to each type.
	 * @return bounds
	 */
	public Bounds bounds(int scope) { return bounds(scope, scope, scope); }
	
	/**
	 * Returns the bounds corresponding to the given scopes.
	 * @return bounds
	 */
	public Bounds bounds(int states, int processes, int mutexes) {
		final List<String> atoms = new ArrayList<String>(states + processes + mutexes);
		for(int i = 0; i < states; i++) {
			atoms.add("State"+i);
		}
		for(int i = 0; i < processes; i++) {
			atoms.add("Process"+i);
		}
		for(int i = 0; i < mutexes; i++) {
			atoms.add("Mutex"+i);
		}
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final TupleSet sb = f.range(f.tuple("State0"), f.tuple("State"+(states-1)));
		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process"+(processes-1)));
		final TupleSet mb = f.range(f.tuple("Mutex0"), f.tuple("Mutex"+(mutexes-1)));
		
		b.bound(State, sb);
		b.bound(holds, sb.product(pb).product(mb));
		b.bound(waits, sb.product(pb).product(mb));
		
		b.bound(sfirst, sb);
		b.bound(slast, sb);
		b.bound(sord, sb.product(sb));
		
		b.bound(Process, pb);
		
		b.bound(Mutex, mb);
		b.bound(mfirst, mb);
		b.bound(mlast, mb);
		b.bound(mord, mb.product(mb));
			
		return b;
	}
	
	private static void usage() {
		System.out.println("Usage: java examples.Dijkstra [# states] [# processes] [# mutexes]");
		System.exit(1);
	}
	
	/**
	 * Usage:  java examples.Dijkstra [# states] [# processes] [# mutexes]
	 */
	public static void main(String[] args) {
		if (args.length < 3)
			usage();
		
		final Dijkstra model = new Dijkstra();
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);

		try {
			final Formula noDeadlocks = model.checkDijkstraPreventsDeadlocks();
			final int states = Integer.parseInt(args[0]);
			final int processes = Integer.parseInt(args[1]);
			final int mutexes = Integer.parseInt(args[2]);
			final Bounds bounds = model.bounds(states, processes, mutexes);
			System.out.println("*****check DijkstraPreventsDeadlocks for " + 
					          states + " State, " + processes + " Process, " + mutexes + " Mutex*****");

			System.out.println(noDeadlocks);
//			System.out.println(bounds);
			Solution sol1 = solver.solve(noDeadlocks, bounds);
			System.out.println(sol1);
//			System.out.println(solver.solve(model.grabOrRelease().and(model.declarations()).
//					and(model.waits.some()).and(model.deadlock()), bounds));
			
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
