package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * KodKod encoding of shakehands.als.
 * 
 * @author Emina Torlak
 */
 public final class Handshake {
	private final Relation Person, Hilary, Jocelyn, shaken, spouse;
	
	public Handshake() {
		Person = Relation.unary("Person");
		Hilary = Relation.unary("Hilary");
		Jocelyn = Relation.unary("Jocelyn");
		shaken = Relation.binary("shaken");
		spouse = Relation.binary("spouse");
	}
	
	/**
	 * Returns the declarations
	 * @return
	 * <pre>
	 * sig Person {spouse: Person, shaken: set Person}
	 * one sig Jocelyn, Hilary extends Person {}
	 * </pre>
	 */
	public Formula declarations() {
		final Formula f0 = spouse.function(Person, Person);
		final Formula f1 = shaken.in(Person.product(Person));
		final Formula f2 = Hilary.one().and(Jocelyn.one());
		return f0.and(f1).and(f2);
	}
	
	/**
	 * Returns the ShakingProtocol fact.
	 * @return
	 * <pre>
	 * fact ShakingProtocol {
	 *  // nobody shakes own or spouse's hand
	 *  all p: Person | no (p + p.spouse) & p.shaken
	 *  // if p shakes q, q shakes p
	 *  all p, q: Person | p in q.shaken => q in p.shaken
	 * }
	 * </pre>
	 */
	public Formula shakingProtocol() {
		final Variable p = Variable.unary("p");
		final Variable q = Variable.unary("q");
		final Formula f1 = p.union(p.join(spouse)).intersection(p.join(shaken)).no().forAll(p.oneOf(Person));
		final Formula f2 = p.in(q.join(shaken)).implies(q.in(p.join(shaken))).forAll(p.oneOf(Person).and(q.oneOf(Person)));
		return f1.and(f2);
	}
	
	/**
	 * Returns the Spouses fact.
	 * @return 
	 * <pre>
	 * fact Spouses {
	 *  all disj p, q: Person {
	 *   // if q is p's spouse, p is q's spouse
	 *   p.spouse = q => q.spouse = p
	 *   // no spouse sharing
	 *	 p.spouse != q.spouse
	 *  }
	 *  all p: Person {
	 * 	 // a person is his or her spouse's spouse
	 *	 p.spouse.spouse = p
	 *	 // nobody is his or her own spouse
	 *	 p != p.spouse
	 *	}
	 * }
	 * </pre>
	 */
	public Formula spouses() {
		final Variable p = Variable.unary("p");
		final Variable q = Variable.unary("q");
		final Formula f1 = p.join(spouse).eq(q).implies(q.join(spouse).eq(p));
		final Formula f2 = p.join(spouse).eq(q.join(spouse)).not();
		final Formula f3 = p.intersection(q).no().implies(f1.and(f2)).forAll(p.oneOf(Person).and(q.oneOf(Person)));
		final Formula f4 = p.join(spouse).join(spouse).eq(p).and(p.eq(p.join(spouse)).not()).forAll(p.oneOf(Person));
		return f3.and(f4);
	}
	
	/**
	 * Returns the Puzzle predicate
	 * @return 
	 * <pre>
	 * pred Puzzle() {
	 *  // everyone but Jocelyn has shaken a different number of hands
	 *  all disj p,q: Person - Jocelyn | #p.shaken != #q.shaken
	 *  // Hilary's spouse is Jocelyn
	 *  Hilary.spouse = Jocelyn
	 * }
	 * </pre>
	 */
	public Formula puzzle() {
		final Variable p = Variable.unary("p");
		final Variable q = Variable.unary("q");
		final Formula f = p.eq(q).not().implies(p.join(shaken).count().eq(q.join(shaken).count()).not());
		final Expression e = Person.difference(Jocelyn);
		return f.forAll(p.oneOf(e).and(q.oneOf(e))).and(Hilary.join(spouse).eq(Jocelyn));
	}
	
	/**
	 * Returns the conjunction of the facts and the puzzle predicate.
	 * @return declarations().and(shakingProtocol()).and(spouses()).and(puzzle())
	 */
	public Formula runPuzzle() {
		return declarations().and(shakingProtocol()).and(spouses()).and(puzzle());
	}
	
	/**
	 * Returns a bounds for the given number of persons.
	 * @return a bounds for the given number of persons.
	 */
	public Bounds bounds(int persons) {
		final List<String> atoms = new ArrayList<String>(persons);
		atoms.add("Hilary"); 
		atoms.add("Jocelyn");
		for(int i = 2; i < persons; i ++) {
			atoms.add("Person" + i);
		}
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		b.boundExactly(Person, f.allOf(1));
		b.boundExactly(Hilary, f.setOf("Hilary"));
		b.boundExactly(Jocelyn, f.setOf("Jocelyn"));
		b.bound(spouse, f.allOf(2));
		b.bound(shaken, f.allOf(2));
		return b;
	}
	
	private static void usage() {
		System.out.println("Usage: java examples.Handshake [# persons, must be >= 2]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.Handshake [# persons, must be >= 2]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		final Handshake model =  new Handshake();
		final Solver solver = new Solver();
		try {
			final int persons = Integer.parseInt(args[0]);
			if (persons<2) usage();
			solver.options().setBitwidth(6);
			
//			solver.options().setSolver(SATFactory.ZChaff);
			solver.options().setSolver(SATFactory.MiniSat);
			
			solver.options().setSymmetryBreaking(0);
			solver.options().setBitwidth(32 - Integer.numberOfLeadingZeros(persons));
			solver.options().setReporter(new ConsoleReporter());
			final Bounds b = model.bounds(persons);
			final Formula f = model.runPuzzle();//.and(model.Person.count().eq(IntConstant.constant(persons)));
			Solution sol = solver.solve(f, b);
			System.out.println(sol);
			
		} catch (NumberFormatException nfe) {
			usage();
		} 
	}
	
}
