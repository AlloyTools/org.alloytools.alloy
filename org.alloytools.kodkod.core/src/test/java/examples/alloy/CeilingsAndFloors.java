package examples.alloy;

import java.util.LinkedList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * A kodkod encoding of ceilingsAndFloors.als
 * 
 * <pre>
 * In his 1973 song, Paul Simon said "One Man's Ceiling Is Another Man's Floor".
 * Does it follow that "One Man's Floor Is Another Man's Ceiling"?
 *
 * To see why not, check the assertion BelowToo.
 *
 * Perhaps simply preventing man's own floor from being his ceiling is enough,
 * as is done in the Geometry constraint.  BelowToo' shows that there are still
 * cases where Geometry holds but the implication does not, although now
 * the smallest solution has 3 Men and 3 Platforms instead of just 2 of each.
 *
 * What if we instead prevent floors and ceilings from being shared,
 * as is done in the NoSharing constraint?  The assertion BelowToo''
 * has no counterexamples, demonstrating that the implication now
 * holds for all small examples.
 *
 * model author: Daniel Jackson (11/2001)
 * modified by Robert Seater (11/2004)
 *
 * sig Platform {}
 * sig Man {ceiling, floor: Platform}
 * fact PaulSimon {all m: Man | some n: Man | Above (n,m)}
 * pred Above(m, n: Man) {m.floor = n.ceiling}
 *
 * assert BelowToo {all m: Man | some n: Man | Above (m,n)}
 * check BelowToo for 2 expect 1
 * 
 * pred Geometry (){no m: Man | m.floor = m.ceiling}
 *  assert BelowToo' {Geometry() => all m: Man | some n: Man | Above (m,n)}
 * check BelowToo' for 2 expect 0
 * check BelowToo' for 3 expect 1
 * 
 * pred NoSharing() {no disj m,n: Man | m.floor = n.floor || m.ceiling = n.ceiling}
 * assert BelowToo'' {NoSharing() => all m: Man | some n: Man | Above (m,n)}
 * check BelowToo'' for 5 expect 0
 * check BelowToo'' for 10 expect 0
 * </pre>
 * @author Emina Torlak
 */
public final class CeilingsAndFloors {
	private final Relation Platform, Man, ceiling, floor;
	
	/**
	 * Creates an instance of the ceilings and floors class.
	 */
	public CeilingsAndFloors() {
		Platform = Relation.unary("Platform");
		Man = Relation.unary("Man");
		ceiling = Relation.binary("ceiling");
		floor = Relation.binary("floor");
	}
	
	/**
	 * Returns a formula that constrains the ceiling and floor 
	 * relations to be functions from Man to Platform.
	 * @return FUNCTION(ceiling, Man, Platform) && FUNCTION(floor, Man, Platform)
	 */
	public Formula declarations() {
		// ceiling and floor are functions from Man to Platform
		return ceiling.function(Man,Platform).and(floor.function(Man,Platform));
	}
	
	/**
	 * Returns the belowToo constraint
	 * @return all m: Man | some n: Man | m.floor = n.ceiling
	 */
	public Formula belowToo() {
		final Variable m = Variable.unary("m0"), n = Variable.unary("n0");
//		 all m: Man | some n: Man | m.floor = n.ceiling
		return ((m.join(floor).eq(n.join(ceiling))).forSome(n.oneOf(Man)).forAll(m.oneOf(Man)));

	}
	
	/**
	 * Returns the noSharing constraint.
	 * @return all m, n: Man | !(m = n) => !(m.floor = n.floor || m.ceiling = n.ceiling) 
	 */
	public Formula noSharing() {
		final Variable m = Variable.unary("m1"), n = Variable.unary("n1");
//		 all m, n: Man | !(m = n) => !(m.floor = n.floor || m.ceiling = n.ceiling) 
		final Formula body = (m.join(floor).eq(n.join(floor))).or(m.join(ceiling).eq(n.join(ceiling)));
		return (m.eq(n).not().implies(body.not())).forAll(m.oneOf(Man).and(n.oneOf(Man)));
	}
	
	/**
	 * Returns the paulSimon constraint.
	 * @return all m: Man | some n: Man | n.floor = m.ceiling
	 */
	public Formula paulSimon() {
		final Variable m = Variable.unary("m2"), n = Variable.unary("n2");
//		 all m: Man | some n: Man | n.floor = m.ceiling
		return ((n.join(floor).eq(m.join(ceiling))).forSome(n.oneOf(Man)).forAll(m.oneOf(Man)));

	}
	
	/**
	 * Returns the belowToo'' constraint.
	 * @return declarations() &&  paulSimon() && noSharing() && !belowToo()
	 */
	public Formula checkBelowTooDoublePrime() {
		return declarations().and(paulSimon()).and(noSharing()).and(belowToo().not());
	}
	
	/**
	 * Returns the belowToo assertion.
	 * @return declarations() && paulSimon() && !belowToo()
	 */
	public Formula checkBelowTooAssertion() {
		return declarations().and(paulSimon()).and(belowToo().not());
	}
	
	/**
	 * Creates bounds for the problem using the given number of platforms and men. 
	 * @return bounds for the problem using the given number of platforms and men. 
	 */
	public Bounds bounds(int scope) { return bounds(scope, scope); }
	
	/**
	 * Creates bounds for the problem using the given number of platforms and men. 
	 * @return bounds for the problem using the given number of platforms and men. 
	 */
	public Bounds bounds(int platforms,int men) {
		final List<String> atoms = new LinkedList<String>();
		for (int i = 0; i < men; i++) {
			atoms.add("Man" + i);
		}
		for (int i = 0; i < platforms; i++) {
			atoms.add("Platform" + i);
		}
		final Universe universe = new Universe(atoms);
		final TupleFactory factory = universe.factory();
		final Bounds bounds = new Bounds(universe);
		final String manMax = "Man" + (men - 1), platformMax = "Platform" + (platforms - 1);
		
		bounds.bound(Platform, factory.range(factory.tuple("Platform0"), factory.tuple(platformMax)));
		bounds.bound(Man, factory.range(factory.tuple("Man0"), factory.tuple(manMax)));
		bounds.bound(ceiling, factory.area(factory.tuple("Man0", "Platform0"), factory.tuple(manMax, platformMax)));
		bounds.bound(floor, factory.area(factory.tuple("Man0", "Platform0"), factory.tuple(manMax, platformMax)));
		
		
		return bounds;
	}
	
	private static void usage() {
		System.out.println("Usage: java examples.CeilingsAndFloors [# men] [# platforms]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.CeilingsAndFloors [# men] [# platforms]
	 */
	public static void main(String[] args) {
		if (args.length < 2) usage();
		
		final CeilingsAndFloors model = new CeilingsAndFloors();
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		try {
			final int m = Integer.parseInt(args[0]);
			final int p = Integer.parseInt(args[1]);
			final Formula show = model.checkBelowTooDoublePrime();
			final Solution sol = solver.solve(show, model.bounds(m,p));
			System.out.println(show);
			System.out.println(sol);
			
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
