/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
package kodkod.examples.sudoku;

import static kodkod.ast.Formula.and;
import static kodkod.ast.Relation.ternary;
import static kodkod.ast.Relation.unary;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.AdaptiveRCEStrategy;
import kodkod.engine.ucore.NCEStrategy;
import kodkod.engine.ucore.SCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

/**
 * A simple encoding of Sudoku, that includes several alternative
 * encodings of the rules.
 * @specfield n: int // the order of this sudoku puzzle
 * @author Emina Torlak
 */
public final class Sudoku {
	private final Relation number = unary("number"), grid  = ternary("grid");
	private final Relation[] region;
	
	/**
	 * Constructs a new instance of (r^2)x(r^2) Sudoku.
	 * @requires r > 1
	 * @ensures this.n = r * r
	 */
	public Sudoku(final int r) { 
		if (r < 2) throw new IllegalArgumentException("r must be greater than 1:  r=" + r);
		region = new Relation[r];
		for(int i =0; i < r; i++) { 
			region[i] = Relation.unary("r"+(i+1));
		}
	}
	
	/**
	 * Returns the relation representing the grid.
	 * @return relation representing the grid.
	 */
	public final Relation grid() { return grid; }
	
	/**
	 * Returns the relation representing the set of numbers.
	 * @return relation representing the set of numbers
	 */
	public final Relation number() { return number; }
	
	/**
	 * Returns the ith region.
	 * @requires 0 <= i < sqrt(this.n)
	 * @return the ith region
	 */
	public final Relation region(int i) { return region[i]; }
	
	/**
	 * Returns grid[x][y].
	 * @return grid[x][y].
	 */
	private final Expression grid(Expression x, Expression y) { 
		return y.join(x.join(grid));
	}
	
	/**
	 * Returns the value of the complete predicate, given the specified rows and columns expressions.
	 * @requires rows.arity = cols.arity = 1
	 * @return complete(rows, cols)
	 */
	private final Formula complete(Expression rows, Expression cols) {
		return number.in(grid(rows,cols));
	}

	/**
	 * Returns the rules of the game that are a bit slower than the other two formulations.
	 * @return rules of the game
	 */
	public final Formula slowRules() { 
		final List<Formula> rules = new ArrayList<Formula>(3+region.length*region.length);

		final Variable x = Variable.unary("x"), y = Variable.unary("y");

		rules.add( grid(x,y).one().forAll(x.oneOf(number).and(y.oneOf(number))) );
		rules.add( complete(x, number).forAll(x.oneOf(number)) );
		rules.add( complete(number, y).forAll(y.oneOf(number)) );
	
		for(Relation rx : region) { 
			for(Relation ry: region) { 
				rules.add( complete(rx, ry) );
			}
		}
		return and(rules); 
	}
		
	/**
	 * Returns the rules of the game that yield better performance than {@linkplain #slowRules()}.
	 * @return rules of the game
	 */
	public final Formula rules() { 
		final List<Formula> rules = new ArrayList<Formula>(3+region.length*region.length);

		final Variable x = Variable.unary("x"), y = Variable.unary("y");
		final Decls decls = x.oneOf(number).and(y.oneOf(number));

		rules.add( grid(x,y).some().forAll(decls) );
		rules.add( grid(x,y).intersection(grid(x, number.difference(y))).no().forAll(decls) );	
		rules.add( grid(x,y).intersection(grid(number.difference(x), y)).no().forAll(decls) );
	
		for(Relation rx : region) { 
			for(Relation ry: region) { 
				rules.add( grid(x, y).intersection(grid(rx.difference(x),ry.difference(y))).no().forAll(x.oneOf(rx).and(y.oneOf(ry))) );
			}
		}
		
		return and(rules); 
	}
	
	/**
	 * Returns a slightly different version of the rules that yields
	 * better performance than {@linkplain #rules()}.
	 * @return rules of the game
	 */
	public final Formula fastRules() { 
		final List<Formula> rules = new ArrayList<Formula>(3+region.length*region.length);

		final Variable x = Variable.unary("x"), y = Variable.unary("y");
		final Decls decls = x.oneOf(number).and(y.oneOf(number));

		rules.add( grid(x,y).one().forAll(decls) );
		rules.add( grid(x,y).intersection(grid(x, number.difference(y))).no().forAll(decls) );	
		rules.add( grid(x,y).intersection(grid(number.difference(x), y)).no().forAll(decls) );
	
		for(Relation rx : region) { 
			for(Relation ry: region) { 
				rules.add( complete(rx, ry) );
			}
		}
		return and(rules); 
	}
	
	/**
	 * Returns the bounds for the default puzzle.
	 * @return bounds for the default puzzle.
	 */
	public static final TupleSet defaultPuzzle() { 
		return SudokuParser.parse("600200050018060020003000400000607800402050000000908000504090300020000014300005007");
	}
		
	/**
	 * Constructs new bounds using the given set of puzzle clues.
	 * @requires clues.universe = {i: Integer | 0 < i <= this.n}
	 * @requires clues.arity = 3
	 * @return new bounds using the given set of puzzle clues.
	 */
	public final Bounds bounds(TupleSet clues) { 
		final int r = region.length;
		final int n = r*r;
		if(clues.universe().size()!=n || clues.arity()!=3) throw new IllegalArgumentException();
		
		final Bounds bounds = new Bounds(clues.universe());
		final TupleFactory f = bounds.universe().factory();
		
		bounds.boundExactly(number, f.allOf(1));
		for(int i = 0; i < r; i++) { 
			bounds.boundExactly(region[i], f.range(f.tuple(i*r+1), f.tuple((i+1)*r)));
		}
		
		final TupleSet givens = clues.clone(), upper = f.allOf(3);
		for(Tuple t : clues) { 
			final int x = (Integer)t.atom(0), y = (Integer)t.atom(1), v = (Integer)t.atom(2);
			for(int i = 1; i<=n; i++ ) {
				if (v!=i) upper.remove(f.tuple(x, y, i));
			}
		}
		
		bounds.bound(grid, givens, upper);
		return bounds;
	}
		
	
	
	/**
	 * Solves the given puzzle using MiniSatProver and translation logging
	 * if core is true; otherwise solves it using MiniSat.  Solution is
	 * printed to standard output.
	 */
	private void solve(TupleSet clues, SudokuCoreExtractor extractor) { 
		final Solver solver = new Solver();
		
		solver.options().setSolver(SATFactory.MiniSatProver);
		solver.options().setLogTranslation(1);
		
				
		final Solution sol = solver.solve(rules(), bounds(clues));
		if (sol.instance()!=null) { 
			System.out.println(sol.stats());	
			System.out.println(SudokuParser.prettyPrint(sol.instance().tuples(grid)));
		} else {
			System.out.println(sol.stats());
			final Proof proof = sol.proof();
			final long[] coreData = extractor.extract(proof);
			System.out.println("Core (strategy="+extractor.name().toLowerCase()+", size="+coreData[0]+", ms="+coreData[1]+"):");
			for(Node n : proof.highLevelCore().values()) { 
				System.out.println(n);
			}
		}
	}
	
	private static void usage() { 
		System.out.println("Usage: java examples.sudoku.Sudoku [-core=<oce|rce|sce|nce>] [puzzle]");
		System.exit(1);
	}
		
	/**
	 * Enumerates core extractors for use with sudoku.
	 * @author Emina Torlak
	 */
	private static enum SudokuCoreExtractor {
		
		OCE {
			long[] extract(Proof proof) { 
				final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
				bean.setThreadCpuTimeEnabled(true);
				final long start = bean.getCurrentThreadUserTime();
				final int initCore = proof.highLevelCore().size();
				final long end = bean.getCurrentThreadUserTime();
				return new long[]{ initCore, toMillis(end-start) };
			}
		},
		RCE,
		SCE,
		NCE;
		
		long[] extract(Proof proof) { 
			final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
			bean.setThreadCpuTimeEnabled(true);
			final ReductionStrategy strategy;
			switch(this) { 
			case RCE : strategy = new AdaptiveRCEStrategy(proof.log()); break;
			case SCE : strategy = new SCEStrategy(proof.log()); break;
			case NCE : strategy = new NCEStrategy(proof.log()); break;
			default : throw new IllegalStateException("Unknown strategy: " + this);
			}
			final long start = bean.getCurrentThreadUserTime();
			proof.minimize(strategy);
			final int minCore = proof.highLevelCore().size();
			final long end = bean.getCurrentThreadUserTime();
			return new long[]{ minCore, toMillis(end-start) };
		}
		
		static long toMillis(long nanos) { return nanos / 1000000; }
	}
	
	/**
	 * Usage: java examples.sudoku.Sudoku [-core=<oce|rce|sce|nce>] [puzzle]
	 */
	public static void main(String[] args) {
		try {
			final TupleSet clues = args.length==0 ? defaultPuzzle() : SudokuParser.parse(args[args.length-1]);
			final SudokuCoreExtractor extractor;
			final Map<String,String> opts = SudokuParser.options(args);
			if (opts.containsKey("-core")) { 
				final String val = opts.get("-core");
				if (val==null) usage();
				extractor = SudokuCoreExtractor.valueOf(SudokuCoreExtractor.class, val.toUpperCase());	
			} else {
				extractor = SudokuCoreExtractor.RCE;
			}

			(new Sudoku((int)Math.sqrt(clues.universe().size()))).solve(clues, extractor);
		} catch (IllegalArgumentException iae) { 
			throw iae;
//			usage();
		}
	}
}



