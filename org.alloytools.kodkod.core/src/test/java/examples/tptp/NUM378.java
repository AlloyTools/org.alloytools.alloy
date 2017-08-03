/**
 * 
 */
package examples.tptp;

import static kodkod.ast.Expression.UNIV;

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
 * A KK encoding of NUM378+1.020.015.p from http://www.cs.miami.edu/~tptp/
 * 
 * @author Emina Torlak
 */
public final class NUM378 {
	private final Relation succ, sum;
	
	/**
	 * Constructs a new instance of NUM378.
	 */
	public NUM378() {
		succ = Relation.binary("succ");
		sum = Relation.ternary("sum");
	}
	
	/**
	 * Returns the expression y.(x.sum)
	 * @return y.(x.sum)
	 */
	final Expression sum(Expression x, Expression y) {
		return y.join(x.join(sum));
	}
	
	/**
	 * Returns the successor of x.
	 * @return x.succ
	 */
	final Expression succ(Expression x) {
		return x.join(succ);
	}
	
	/**
	 * Returns the predecessor of x.
	 * @return succ.x
	 */
	final Expression pred(Expression x) {
		return succ.join(x);
	}
	
	/**
	 * Returns the declarations.
	 * @return one a && one b && one c
	 */
	public final Formula decls() { 
		final Variable x = Variable.unary("X");
		final Variable y = Variable.unary("Y");
		return succ.function(UNIV, UNIV).
			and(sum(x,y).one().forAll(x.oneOf(UNIV).and(y.oneOf(UNIV))));
	}
	
	private final Variable[] vars(String name, int size) {
		final Variable[] vars = new Variable[size];
		for(int i = 0; i < size; i++) {
			vars[i] = Variable.unary(name + i);
		}
		return vars;
	}
	
	private final Decls decls(Variable[] vars) {
		Decls d = vars[0].oneOf(UNIV);
		for(int i = 1; i < vars.length; i++) {
			d = d.and(vars[i].oneOf(UNIV));
		}
		return d;
	}
	
	/**
	 * Returns the try_satisfy_this axiom.
	 * @return try_satisfy_this
	 */
	public final Formula inequalities() {
		final Variable[] x = vars("X",16);
		final Variable[] y = vars("Y",16);
		final Variable[] npx = vars("NPX",15);
		final Variable[] nsx = vars("NSX",15);
		final Variable[] npy = vars("NPY",15);
		final Variable[] nsy = vars("NSY",15);
		
		Expression s21 = succ;
		for(int i = 1; i < 21; i++) {
			s21 = s21.join(succ);
		}
		
		Formula f = Formula.TRUE;
		
		for(int i = 0; i < 15; i++) {
			Formula f0 = npx[i].eq(s21.join(x[i]));
			Formula f1 = nsx[i].eq(x[i].join(s21));
			Formula f2 = npy[i].eq(s21.join(y[i]));
			Formula f3 = nsy[i].eq(y[i].join(s21));
			f = f.and(f0).and(f1).and(f2).and(f3);
		}
		
		for(int i = 1; i < 16; i++) {
			Formula f0 = x[i].eq(sum(sum(pred(x[i-1]),succ(y[i-1])),sum(pred(y[i-1]),succ(x[i-1]))));
			Formula f1 = y[i].eq(sum(pred(nsx[i-1]),sum(succ(npx[i-1]),sum(pred(nsy[i-1]),succ(npy[i-1])))));
			f = f.and(f0).and(f1);
		}
		
		Formula g = Formula.FALSE;
		for(int i = 12; i < 16; i++) {
			g = g.or(x[i].eq(y[i]).not());
		}

		return f.and(g).
			forSome(decls(x).and(decls(y)).and(decls(npx)).and(decls(nsx)).and(decls(npy)).and(decls(nsy)));
	}
	
	/**
	 * Returns the conjunction of the axioms and the hypothesis.
	 * @return axioms() && inequalities()
	 */
	public final Formula checkInequalities() { 
		return decls().and(inequalities());
	}
	
	/**
	 * Returns bounds for the problem.
	 * @return bounds for the problem.
	 */
	public final Bounds bounds() {
		final int n = 21;
		final List<String> atoms = new ArrayList<String>(n);
		atoms.add("goal");
		for(int i = 0; i < n; i++)
			atoms.add("n"+i);
		final Universe u = new Universe(atoms);
		final Bounds bound = new Bounds(u);
		final TupleFactory f = u.factory();
		
		final TupleSet succBound = f.noneOf(2);
		for(int i = 0; i < n; i++) {
			succBound.add(f.tuple("n"+i,"n"+((i+1)%n)));
		}
		bound.boundExactly(succ, succBound);
		
		final TupleSet sumBound = f.noneOf(3);
		for(int i = 0; i < n; i++) {
			for(int j = 0; j < n; j++) {
				sumBound.add(f.tuple("n"+i, "n"+j, "n"+((i+j)%n)));
			}
		}
		bound.boundExactly(sum, sumBound);
		return bound;
	}
	
	private static void usage() {
		System.out.println("java examples.tptp.NUM378");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.tptp.NUM378
	 */
	public static void main(String[] args) {
	
		try {
	
			final NUM378 model = new NUM378();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			final Formula f = model.decls().and(model.inequalities());
			final Bounds b = model.bounds();
//			System.out.println(f);
//			System.out.println(b);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol.outcome());
			System.out.println(sol.stats());
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
	
}
