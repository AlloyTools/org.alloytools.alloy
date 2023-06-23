/**
 * 
 */
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A KK encoding of lists.als
 * 
 * @author Emina Torlak
 */
public final class ListsP {
	/*
	 * KK outperformed by the sequential analysis tool on the reflexive and
	 * symmetric assertions
	 */
	private final Relation Thing, List, NonEmptyList, EmptyList;
	private final Relation car, cdr, equivTo, prefixes;
	private static Universe u;

	/**
	 * Constructs a new instance of the Lists model.
	 */
	public ListsP() {
		Thing = Relation.unary("Thing");
		List = Relation.unary("List");
		NonEmptyList = Relation.unary("NonEmptyList");
		EmptyList = Relation.unary("EmptyList");
		car = Relation.binary("car");
		cdr = Relation.binary("cdr");
		equivTo = Relation.binary("equivTo");
		prefixes = Relation.binary("prefixes");
	}

	/**
	 * Returns the declaration constraints.
	 * 
	 * @return declaration constraints
	 */
	public final Formula decls1() {
		// abstract sig List {
		// equivTo: set List,
		// prefixes: set List
		// }
		// sig NonEmptyList extends List {
		// car: one Thing,
		// cdr: one List
		// }
		// sig EmptyList extends List {}
		final Formula f0 = List.eq(EmptyList.union(NonEmptyList));
		final Formula f1 = EmptyList.intersection(NonEmptyList).no();

		final Formula f3 = prefixes.in(List.product(List));

		return f0.and(f1).and(f3);
	}

	public final Formula decls2() {
		final Formula f2 = equivTo.in(List.product(List));
		final Formula f5 = cdr.function(NonEmptyList, List);
		final Formula f4 = car.function(NonEmptyList, Thing);

		return f2.and(f4).and(f5);
	}

	
	/**
	 * Returns all facts in the model.
	 * 
	 * @return the facts.
	 */
	public final Formula facts1() {

		// fact NoStrayThings {Thing in List.car}
		// fact finite {all L: List | isFinite(L)}
		// fact Equivalence {
		// all a,b: List | (a in b.equivTo) <=> (a.car = b.car and b.cdr in
		// a.cdr.equivTo)
		// }

		// fact prefix { //a is a prefix of b
		// List->EmptyList in prefixes
		// all a,b: NonEmptyList | (a in b.prefixes) <=> (a.car = b.car
		// and a.cdr in b.cdr.prefixes)
		// }

		final Formula f7 = List.product(EmptyList).in(prefixes);

//		final Variable a = Variable.unary("a");
//		final Variable b = Variable.unary("b");
//		final Formula f3 = a.join(car).eq(b.join(car));
		

		
		return (f7);
	}
	
	public final Formula facts2() {
		final Formula f0 = Thing.in(List.join(car));
		final Variable L = Variable.unary("L");
		final Formula f1 = isFinite(L).forAll(L.oneOf(List));
		
		final Variable a = Variable.unary("a");
		final Variable b = Variable.unary("b");
		final Formula f2 = a.in(b.join(equivTo));
		final Formula f3 = a.join(car).eq(b.join(car));
		final Formula f4 = b.join(cdr).in(a.join(cdr).join(equivTo));
		final Formula f6 = f2.iff(f3.and(f4)).forAll(a.oneOf(List).and(b.oneOf(List)));
	
		final Formula f8 = a.in(b.join(prefixes));
		final Formula f9 = a.join(cdr).in(b.join(cdr).join(prefixes));
		final Formula f11 = f8.iff(f3.and(f9)).forAll(a.oneOf(NonEmptyList).and(b.oneOf(NonEmptyList)));
		
		return f6.and(f11).and(f0).and(f1);
	}

	/**
	 * Returns the isFinite predicate.
	 * 
	 * @return isFinite
	 */
	public final Formula isFinite(Expression/* List */L) {
		// pred isFinite (L:List) {some EmptyList & L.*cdr}
		return EmptyList.intersection(L.join(cdr.reflexiveClosure())).some();
	}

	/**
	 * Returns the reflexive assertion.
	 * 
	 * @return reflexive
	 */
	public final Formula reflexive() {
		// assert reflexive {all L: List | L in L.equivTo}
		final Variable L = Variable.unary("L");
		return L.in(L.join(equivTo)).forAll(L.oneOf(List));
	}

	/**
	 * Returns the symmetric assertion.
	 * 
	 * @return symmetric
	 */
	public final Formula symmetric() {
		// assert symmetric { ~equivTo in equivTo }
		return equivTo.transpose().in(equivTo);
	}

	/**
	 * Returns the empties assertion.
	 * 
	 * @return empties
	 */
	public final Formula empties() {
		// assert empties { EmptyList->EmptyList in equivTo}
		return EmptyList.product(EmptyList).in(equivTo);
	}

	/**
	 * Returns the show predicate.
	 * 
	 * @return show
	 */
	public final Formula show() {
		// pred show() {
		// some disj a, b: NonEmptyList | b in a.prefixes
		// }
		final Variable a = Variable.unary("a"), b = Variable.unary("b");
		return a.eq(b).not().and(b.in(a.join(prefixes))).forSome(a.oneOf(NonEmptyList).and(b.oneOf(NonEmptyList)));
	}

	/**
	 * Returns the conjunction of declaration constraints and facts.
	 * 
	 * @return decls() and facts()
	 */
	public final Formula invariants1() {
		return decls1().and(facts1());
	}
	
	public final Formula invariants2() {
		return decls2().and(facts2());
	}

	/**
	 * Returns the conjunction of invariants and the show predicate.
	 * 
	 * @return invariants() and show()
	 */
	public final Formula runShow1() {
		return invariants1().and(show());
	}
	
	public final Formula runShow2() {
		return invariants2();
	}

	/**
	 * Returns the conjunction of invariants and the negation of the empty
	 * hypothesis.
	 * 
	 * @return invariants() and !empties()
	 */
	public final Formula checkEmpties1() {
		return invariants1().and(empties().not());
	}
	
	public final Formula checkEmpties2() {
		return invariants2();
	}

	/**
	 * Returns the conjunction of invariants and the negation of the reflexive
	 * hypothesis.
	 * 
	 * @return invariants() and !reflexive()
	 */
	public final Formula checkReflexive1() {
		return invariants1();
	}
	
	public final Formula checkReflexive2() {
		return invariants2().and(reflexive().not());
	}

	/**
	 * Returns the conjunction of invariants and the negation of the symmetric
	 * hypothesis.
	 * 
	 * @return invariants() and !symmetric()
	 */
	public final Formula checkSymmetric1() {
		return invariants1();
	}
	
	public final Formula checkSymmetric2() {
		return invariants2().and(symmetric().not());
	}


	/**
	 * Returns the bounds for the given scope.
	 * 
	 * @return the bounds for the given scope.
	 */
	public final Bounds bounds1(int scope) {
		assert scope > 0;
		final int n = scope * 2;
		final List<String> atoms = new ArrayList<String>(n);
		for (int i = 0; i < scope; i++)
			atoms.add("Thing" + i);
		for (int i = 0; i < scope; i++)
			atoms.add("List" + i);

		// private final Relation Thing, List, NonEmptyList, EmptyList;
		// private final Relation car, cdr, equivTo, prefixes;
		u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final int max = scope - 1;

		f.range(f.tuple("Thing0"), f.tuple("Thing" + max));
		TupleSet lb = f.range(f.tuple("List0"), f.tuple("List" + max));

		b.boundExactly(List, lb);
		b.bound(EmptyList, lb);
		b.bound(NonEmptyList, lb);


		b.bound(prefixes, lb.product(lb));
		return b;
	}

	public final Bounds bounds2(int scope) {
		assert scope > 0;
		// private final Relation Thing, List, NonEmptyList, EmptyList;
		// private final Relation car, cdr, equivTo, prefixes;
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final int max = scope - 1;

		TupleSet tb = f.range(f.tuple("Thing0"), f.tuple("Thing" + max));
		TupleSet lb = f.range(f.tuple("List0"), f.tuple("List" + max));
		b.bound(equivTo, lb.product(lb));
		b.bound(Thing, tb);
		b.bound(car, lb.product(tb));
		b.bound(cdr, lb.product(lb));

		return b;
	}

	private static void usage() {
		System.out.println("java examples.Lists [scope]");
		System.exit(1);
	}

	/**
	 * Usage: java examples.Lists [scope]
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws InterruptedException {
		if (args.length < 1)
			usage();
		try {
			final int n = Integer.parseInt(args[0]);
			final ListsP model = new ListsP();

			final Bounds b1 = model.bounds1(n);
			final Bounds b2 = model.bounds2(n);
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.Glucose);
			solver.options().setSymmetryBreaking(20);;

			Bounds b3 = b1.clone();
			for (Relation r : b2.relations()) {
				b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
			}

			Formula f1 = model.checkSymmetric1();
			Formula f2 = model.checkSymmetric2();
			
//			System.out.println("running show");
			long start = System.currentTimeMillis();

			Solution s = solver.solve(f1.and(f2), b3);
			long end = System.currentTimeMillis();
			System.out.println(end - start);

//			System.out.println(s);
//
//			f = model.checkEmpties();
//			System.out.println("checking empties");
//			s = solver.solve(f, b1);
//			System.out.println(s);

			ExtendedOptions opt, opt2;
			
			opt = new ExtendedOptions();
			opt.setSymmetryBreaking(20);
			opt.setSolver(SATFactory.Glucose);
			opt.setDecomposedMode(DMode.PARALLEL);
			opt.setThreads(4);
			opt2 = new ExtendedOptions(opt);
			opt2.setRunTarget(false);
			opt2.setSymmetryBreaking(20);

			opt.setConfigOptions(opt2);
			new PardinusSolver(opt);
			
		
			System.out.println("checking reflexive: "+f1);
			start = System.currentTimeMillis();
//			psolver.solve(f1, f2, b1, b2);
			end = System.currentTimeMillis();
			System.out.println(end - start);

//			Solution s = solver.solve(f1.and(f2), b1);
			System.out.println(s);

//			f = model.checkSymmetric();
//			System.out.println("checking symmetric");
//			s = solver.solve(f, b1);
//			System.out.println(s);

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
