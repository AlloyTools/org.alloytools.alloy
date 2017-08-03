/**
 * 
 */
package examples.alloy;

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
import kodkod.instance.Universe;

/**
 * A KK encoding of lists.als
 * @author Emina Torlak
 */
public final class Lists {
	/* KK outperformed by the sequential analysis tool on the reflexive and symmetric assertions */
	private final Relation Thing, List, NonEmptyList, EmptyList;
	private final Relation car, cdr, equivTo, prefixes;
	
	/**
	 * Constructs a new isntance of the Lists model.
	 */
	public Lists() {
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
	 * @return declaration constraints
	 */
	public final Formula decls() {
//		abstract sig List {
//			equivTo: set List,
//			prefixes: set List
//			}
//		sig NonEmptyList extends List {
//			car: one Thing,
//			cdr: one List
//			}
//		sig EmptyList extends List {}
		final Formula f0 = List.eq(EmptyList.union(NonEmptyList));
		final Formula f1 = EmptyList.intersection(NonEmptyList).no();
		final Formula f2 = equivTo.in(List.product(List));
		final Formula f3 = prefixes.in(List.product(List));
		final Formula f4 = car.function(NonEmptyList, Thing);
		final Formula f5 = cdr.function(NonEmptyList, List);
		return f0.and(f1).and(f2).and(f3).and(f4).and(f5);
	}

	/**
	 * Returns all facts in the model.
	 * @return the facts.
	 */
	public final Formula facts() {
		// fact NoStrayThings {Thing in List.car}
		final Formula f0 = Thing.in(List.join(car));
//		fact finite {all L: List | isFinite(L)}
		final Variable L = Variable.unary("L");
		final Formula f1 = isFinite(L).forAll(L.oneOf(List));
//		fact Equivalence {
//			all a,b: List | (a in b.equivTo) <=> (a.car = b.car and b.cdr in a.cdr.equivTo)
//			}
		final Variable a = Variable.unary("a");
		final Variable b = Variable.unary("b");
		final Formula f2 = a.in(b.join(equivTo));
		final Formula f3 = a.join(car).eq(b.join(car));
		final Formula f4 = b.join(cdr).in(a.join(cdr).join(equivTo));
		final Formula f6 = f2.iff(f3.and(f4)).forAll(a.oneOf(List).and(b.oneOf(List)));
//		fact prefix { //a is a prefix of b
//			List->EmptyList in prefixes
//		     all a,b: NonEmptyList | (a in b.prefixes) <=> (a.car = b.car
//				and a.cdr in b.cdr.prefixes)
//		}
		final Formula f7 = List.product(EmptyList).in(prefixes);
		final Formula f8 = a.in(b.join(prefixes));
		final Formula f9 = a.join(cdr).in(b.join(cdr).join(prefixes));
		final Formula f11 = f8.iff(f3.and(f9)).forAll(a.oneOf(NonEmptyList).and(b.oneOf(NonEmptyList)));
			
		return f0.and(f1).and(f6).and(f7).and(f11);
	}

	/**
	 * Returns the isFinite predicate.
	 * @return isFinite
	 */
	public final Formula isFinite(Expression/*List*/ L) {
//		pred isFinite (L:List) {some EmptyList & L.*cdr}
		return EmptyList.intersection(L.join(cdr.reflexiveClosure())).some();
	}
	
	
	/**
	 * Returns the reflexive assertion.
	 * @return reflexive
	 */
	public final Formula reflexive() {
//		assert reflexive {all L: List | L in L.equivTo}
		final Variable L = Variable.unary("L");
		return L.in(L.join(equivTo)).forAll(L.oneOf(List));
	}
	
	/**
	 * Returns the symmetric assertion.
	 * @return symmetric
	 */
	public final Formula symmetric() {
//		assert symmetric { ~equivTo in equivTo }
		return equivTo.transpose().in(equivTo);
	}
	
	/**
	 * Returns the empties assertion.
	 * @return empties
	 */
	public final Formula empties() {
//		assert empties { EmptyList->EmptyList in equivTo}
		return EmptyList.product(EmptyList).in(equivTo);
	}
	
	/**
	 * Returns the show predicate.
	 * @return show
	 */
	public final Formula show() {
//		pred show() {
//			some disj a, b: NonEmptyList | b in a.prefixes
//			}
		final Variable a = Variable.unary("a"), b = Variable.unary("b");
		return a.eq(b).not().and(b.in(a.join(prefixes))).forSome(a.oneOf(NonEmptyList).and(b.oneOf(NonEmptyList)));
	}
	
	/**
	 * Returns the conjunction of declaration constraints and facts.
	 * @return decls() and facts()
	 */
	public final Formula invariants() { 
		return decls().and(facts());
	}
	
	/**
	 * Returns the conjunction of invariants and the show predicate.
	 * @return invariants() and show()
	 */
	public final Formula runShow() { 
		return invariants().and(show());
	}
	
	/**
	 * Returns the conjunction of invariants and the negation of the empty hypothesis.
	 * @return invariants() and !empties()
	 */
	public final Formula checkEmpties() { 
		return invariants().and(empties().not());
	}
	
	/**
	 * Returns the conjunction of invariants and the negation of the reflexive hypothesis.
	 * @return invariants() and !reflexive()
	 */
	public final Formula checkReflexive() { 
		return invariants().and(reflexive().not());
	}
	
	/**
	 * Returns the conjunction of invariants and the negation of the symmetric hypothesis.
	 * @return invariants() and !symmetric()
	 */
	public final Formula checkSymmetric() { 
		return invariants().and(symmetric().not());
	}
	
	/**
	 * Returns the bounds for the given scope.
	 * @return the bounds for the given scope.
	 */
	public final Bounds bounds(int scope) {
		assert scope > 0;
		final int n = scope*2;
		final List<String> atoms = new ArrayList<String>(n);
		for(int i = 0; i < scope; i++)
			atoms.add("Thing"+i);
		for(int i = 0; i < scope; i++)
			atoms.add("List"+i);
		
		//private final Relation Thing, List, NonEmptyList, EmptyList;
		//private final Relation car, cdr, equivTo, prefixes;
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final int max = scope-1;
		
		b.bound(Thing, f.range(f.tuple("Thing0"), f.tuple("Thing"+max)));
		b.bound(List, f.range(f.tuple("List0"), f.tuple("List"+max)));
		b.bound(EmptyList, b.upperBound(List));
		b.bound(NonEmptyList, b.upperBound(List));
		
		b.bound(car, b.upperBound(List).product(b.upperBound(Thing)));
		b.bound(cdr, b.upperBound(List).product(b.upperBound(List)));
		b.bound(equivTo, b.upperBound(cdr));
		b.bound(prefixes, b.upperBound(cdr));
		return b;
	 }
	
	private static void usage() {
		System.out.println("java examples.Lists [scope]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.Lists [scope]
	 */
	public  static void main(String[] args) {
		if (args.length < 1)
			usage();
		try {
			final int n = Integer.parseInt(args[0]);
			final Lists model = new Lists();
			
			final Bounds b = model.bounds(n);
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
//			solver.options().setFlatten(false);
//			solver.options().setSkolemize(false);
			
			Formula f = model.runShow();
			System.out.println("running show");
			Solution s = solver.solve(f, b);
			System.out.println(s);
		
			f = model.checkEmpties();
			System.out.println("checking empties");
			s = solver.solve(f, b);
			System.out.println(s);
			
			f = model.checkReflexive();
			System.out.println("checking reflexive");
			s = solver.solve(f, b);
			System.out.println(s);
			
			f = model.checkSymmetric();
			System.out.println("checking symmetric");
			s = solver.solve(f, b);
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
