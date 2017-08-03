package examples.alloy;

import java.util.ArrayList;
import java.util.List;

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
 * A KodKod encoding of the pigeonhole problem: module internal/pigeonhole
 * <pre> 
 * sig Pigeon { hole: Hole }
 * 
 * sig Hole {}
 * 
 * pred aPigeonPerHole() { 
 * // holes are not shared 
 *  no disj p1, p2: Pigeon |
 *   p1.hole = p2.hole }
 * 
 * run aPigeonPerHole for exactly 30 Pigeon, exactly 29 Hole
 * </pre>
 * @author Emina Torlak
 */
public final class Pigeonhole {
	//	 sigs
	private final Relation Pigeon, Hole;
	// fields
	private final Relation hole;
	
	/**
	 * Creates an instance of the pigeonhole example.
	 */
	public Pigeonhole() {
		this.Pigeon = Relation.unary("Pigeon");
		this.Hole = Relation.unary("Hole");
		this.hole = Relation.binary("hole");		
	}
	
	/**
	 * Returns the declaration constraints.
	 * @return declarations
	 */
	public Formula declarations() {
		return hole.function(Pigeon, Hole);
	}
	
	/**
	 * Returns the aPigeonPerHole constraints.
	 * @return aPigeonPerHole
	 */
	public Formula pigeonPerHole() {
		final Variable p1 = Variable.unary("p1");
		final Variable p2 = Variable.unary("p2");
		return (p1.eq(p2).not().
				implies(p1.join(hole).intersection(p2.join(hole)).no())).
				forAll(p1.oneOf(Pigeon).and(p2.oneOf(Pigeon)));
	}
	
	/**
	 * Returns the bounds for the given number of pigeons and holes.
	 * @return bounds
	 */
	public Bounds bounds(int pigeons, int holes) {
		final List<String> atoms = new ArrayList<String>(pigeons + holes);
		for(int i = 0; i < pigeons; i++) {
			atoms.add("Pigeon"+i);
		}
		for(int i = 0; i < holes; i++) {
			atoms.add("Hole"+i);
		}
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		
		final Bounds b = new Bounds(u);
		
		final TupleSet pbound = f.range(f.tuple("Pigeon0"), f.tuple("Pigeon" + (pigeons-1)));
		final TupleSet hbound = f.range(f.tuple("Hole0"), f.tuple("Hole" + (holes-1)));
		b.boundExactly(Pigeon, pbound);
		b.boundExactly(Hole, hbound);
		b.bound(hole, pbound.product(hbound));
		return b;
	}
	
	private static void usage() {
		System.out.println("Usage: java tests.Pigeonhole [# pigeons] [# holes]");
		System.exit(1);
	}
	
	/**
	 * Usage: java tests.Pigeonhole [# pigeons] [# holes]
	 */
	public static void main(String[] args) {
		if (args.length < 2)
			usage();
		final Pigeonhole model = new Pigeonhole();
		final Solver solver = new Solver();
		
		try {
			final int p = Integer.parseInt(args[0]);
			final int h = Integer.parseInt(args[1]);
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setSymmetryBreaking(p);
			final Formula show = model.declarations().and(model.pigeonPerHole());
			final Solution sol = solver.solve(show, model.bounds(p,h));
			//System.out.println(show);
			System.out.println(sol);
			
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
