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
package kodkod.examples.csp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Various Kodkod encodings of the nqueens problem 
 * (purely relational, an explicitly encoding that 
 * uses integers, and a smarter integer encoding
 * that uses a logarithmic number of bits).
 * 
 * @author Emina Torlak
 */
public abstract class NQueens {
	
	
	/**
	 * Returns an encoding of the problem.
	 * @return an encoding of the problem.
	 */
	public abstract Formula rules();
	
	/**
	 * Returns a bounds for this encoding of the nqueens problem.
	 * @return bounds for this encoding of the nqueens problem.
	 */
	public abstract Bounds bounds();
	
	/**
	 * Prints the given solution using the given options to the console
	 */
	abstract void print(Instance instance, Options options);
	
	
	
	private static void usage() { 
		System.out.println("Usage:  java NQueens <positive number of queens> <encoding: int | log | rel>");
		System.exit(1);
	}
	
	
	/**
	 * Usage:  java NQueens <number of queens> <encoding: int | log | rel>
	 */
	public static void main(String[] args) { 
		if (args.length < 2)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1 || n <= 0)
				usage();
			
			final NQueens model; 
			if (args[1].compareToIgnoreCase("int")==0) {
				model = new IntQueens(n);
			} else if (args[1].compareToIgnoreCase("log")==0) {
				model = new LogQueens(n);
			} else if (args[1].compareToIgnoreCase("rel")==0) {
				model = new RelQueens(n);
			} else {
				usage();
				return;
			}
			
			final Formula f = model.rules();
			final Bounds b = model.bounds();
			final Solver s = new Solver();
//			System.out.println(b);
			System.out.println("encoding:");
			System.out.println(PrettyPrinter.print(f, 1));

			s.options().setSolver(SATFactory.MiniSat);
			s.options().setBitwidth(33 - Integer.numberOfLeadingZeros(n - 1));
			s.options().setReporter(new ConsoleReporter());
			
			final Solution sol = s.solve(f, b);
			
			if (sol.instance()!=null) { 
				System.out.println("solution:");
				model.print(sol.instance(), s.options());
			} else {
				System.out.println("no solution");
			}
			System.out.println(sol.stats());
			
		} catch (NumberFormatException nfe) { 
			usage();
		}
		
	}
	
	/**
	 * A relational encoding of nqueens.
	 * @author Emina Torlak
	 */
	private static class RelQueens extends NQueens {
		private final Relation queen, x, y, num, ord;
		private final int n;
		
		RelQueens(int n) {
			assert n > 0;
			this.n = n;
			this.queen = Relation.unary("Queen");
			this.x = Relation.binary("x");
			this.y = Relation.binary("y");
			this.num = Relation.unary("num");
			this.ord = Relation.binary("ord");
			
		}
		
		/**
		 * Returns a relational encoding of the problem.
		 * @return a relational encoding of the problem.
		 */
		public Formula rules() {
			final List<Formula> rules = new ArrayList<Formula>();
			
			rules.add(x.function(queen, num));
			rules.add(y.function(queen, num));
			
			final Variable i = Variable.unary("n");
			// at most one queen in each row: all i: num | lone x.i
			
			rules.add(x.join(i).lone().forAll(i.oneOf(num)));
			
			// at most one queen in each column: all i: num | lone y.i
			rules.add(y.join(i).lone().forAll(i.oneOf(num)));

			final Variable q1 = Variable.unary("q1"), q2 = Variable.unary("q2");
			
			// at most one queen on each diagonal
			//			all q1: Queen, q2: Queen - q1 |
			//		let xu = prevs[q2.x] + prevs[q1.x],
			//		     xi =  prevs[q2.x] & prevs[q1.x],
			//                yu = prevs[q2.y] + prevs[q1.y],
			//                yi = prevs[q2.y] & prevs[q1.y] |
			//		#(xu - xi) != #(yu - yi)
			final Expression ordClosure = ord.closure();
			final Expression q2xPrevs = ordClosure.join(q2.join(x)), q1xPrevs = ordClosure.join(q1.join(x));
			final Expression q2yPrevs = ordClosure.join(q2.join(y)), q1yPrevs = ordClosure.join(q1.join(y));
			
			final IntExpression xDiff = (q2xPrevs.union(q1xPrevs)).difference(q2xPrevs.intersection(q1xPrevs)).count();
			final IntExpression yDiff = (q2yPrevs.union(q1yPrevs)).difference(q2yPrevs.intersection(q1yPrevs)).count();
			
			rules.add(xDiff.eq(yDiff).not().forAll(q1.oneOf(queen).and(q2.oneOf(queen.difference(q1)))));
			
			return Formula.and(rules);
		}
		
		/**
		 * Returns the bounds for relational encoding of the problem.
		 * @return the bounds for relational encoding of the problem.
		 */
		public Bounds bounds() {
			final List<Object> atoms = new ArrayList<Object>(n*2);
			for(int i =0; i < n; i++) { 
				atoms.add("Q"+i);
			}
			
			for(int i =0; i < n; i++) { 
				atoms.add(Integer.valueOf(i));
			}
			
			final Universe u = new Universe(atoms);
			final Bounds b = new Bounds(u);
			final TupleFactory f = u.factory();
			
			final TupleSet qbound = f.range(f.tuple("Q0"), f.tuple("Q"+(n-1)));
			final TupleSet nbound = f.range(f.tuple(Integer.valueOf(0)), f.tuple(Integer.valueOf(n-1)));
			
			b.boundExactly(queen, qbound);
			b.boundExactly(num, nbound);
			b.bound(x, qbound.product(nbound));
			b.bound(y, qbound.product(nbound));
			
			final TupleSet obound = f.noneOf(2);
			for(int i = 1; i < n; i++) { 
				obound.add(f.tuple((Object)Integer.valueOf(i-1), Integer.valueOf(i)));
			}
			
			b.boundExactly(ord, obound);
			
			for(int i = 0; i < n; i++) { 
				b.boundExactly(i, f.setOf(Integer.valueOf(i)));
			}
			
			return b;
		}
		
		/**
		 * Prints the given solution
		 */
		void print(Instance instance, Options options) {
			final Evaluator eval = new Evaluator(instance, options);
			for(int i = 0; i < n; i++) { 
				Expression ci = IntConstant.constant(i).toExpression();
				for(int j = 0; j < n; j++) { 
					Expression cj = IntConstant.constant(j).toExpression();
					if (eval.evaluate(x.join(ci).intersection(y.join(cj)).some())) { 
						System.out.print(" Q");
					} else {
						System.out.print(" .");
					}
				}
				System.out.println();
			}
//			System.out.println(instance); 
		}
		
		
		
	}
	
	/**
	 * A log encoding of nqueens
	 * @author Emina Torlak
	 */
	private static class LogQueens extends NQueens {
		private final Relation queen, x, y;
		private final int n;
		/**
		 * Constructs an nqueens instance for the given n.
		 */
		LogQueens(int n) {
			assert n > 0;
			this.n = n;
			this.queen = Relation.unary("Queen");
			this.x = Relation.binary("x");
			this.y = Relation.binary("y");
		}
		
		/**
		 * Returns an log integer encoding of the problem.
		 * @return an log integer encoding of the problem.
		 */
		public Formula rules() {
			final List<Formula> rules = new ArrayList<Formula>();
			
			
			final Variable q1 = Variable.unary("q1"), q2 = Variable.unary("q2");
			
			// max row number is less than the number of queens
			// all q1: Queen | q1.x <= #queen-1
			final IntExpression nlessOne = IntConstant.constant(n-1);
			rules.add(q1.join(x).sum().lte(nlessOne).forAll(q1.oneOf(queen)));
			
			// max col number is less than the number of queens
			// all q1: Queen | q1.y <= #queen-1
			rules.add(q1.join(y).sum().lte(nlessOne).forAll(q1.oneOf(queen)));
			
			// at most one queen in each row: 
			// all q1, a2: Queen | q1.x = q2.x => q1 = q2
			rules.add(q1.join(x).eq(q2.join(x)).implies(q1.eq(q2)).forAll(q1.oneOf(queen).and(q2.oneOf(queen))));
				
			// at most one queen in each column:
			// all q1, a2: Queen | q1.y = q2.y => q1 = q2
			rules.add(q1.join(y).eq(q2.join(y)).implies(q1.eq(q2)).forAll(q1.oneOf(queen).and(q2.oneOf(queen))));

			// at most one queen on each diagonal :
			// all q1: Queen, q2: Queen - q1 | abs[q2.x - q1.x] != abs[q2.y - q1.y]
			
			final IntExpression xAbsDiff = q2.join(x).sum().minus(q1.join(x).sum()).abs();
			final IntExpression yAbsDiff = q2.join(y).sum().minus(q1.join(y).sum()).abs();
					
			rules.add(xAbsDiff.eq(yAbsDiff).not().forAll(q1.oneOf(queen).and(q2.oneOf(queen.difference(q1)))));
		
			return Formula.and(rules);
		}
		
		/**
		 * Returns a bounds for the log integer encoding.
		 * @return bounds for the log integer encoding.
		 */
		public Bounds bounds() { 
			final int bits = 32 - Integer.numberOfLeadingZeros(n - 1);
			final List<Object> atoms = new ArrayList<Object>(n + bits);
			for(int i =0; i < n; i++) { 
				atoms.add("Q"+i);
			}
			for(int i = 0; i < bits; i++) { 
				atoms.add(Integer.valueOf(1<<i));
			}
			
			final Universe u = new Universe(atoms);
			final Bounds b = new Bounds(u);
			final TupleFactory f = u.factory();
			
			final TupleSet queens = f.range(f.tuple("Q0"), f.tuple("Q"+(n-1)));
			final TupleSet ints = f.range(f.tuple(Integer.valueOf(1)), f.tuple(Integer.valueOf(1<<(bits-1))));
			
			b.boundExactly(queen, queens);
			b.bound(x, queens.product(ints));
			b.bound(y, queens.product(ints));
			
			for(int i = 0; i < bits; i++) { 
				b.boundExactly(1<<i, f.setOf(Integer.valueOf(1<<i)));
			}
			
			return b;
		}
	
		/**
		 * Prints the given solution
		 */
		void print(Instance instance, Options options) { 
			final Evaluator eval = new Evaluator(instance, options);
			for(int i = 0; i < n; i++) { 
				IntExpression ci = IntConstant.constant(i);
				for(int j = 0; j < n; j++) { 
					IntExpression cj = IntConstant.constant(j);
					Variable q = Variable.unary("q");
					if (eval.evaluate(q.join(x).sum().eq(ci).and(q.join(y).sum().eq(cj)).forSome(q.oneOf(queen)))) { 
						System.out.print(" Q");
					} else {
						System.out.print(" .");
					}
				}
				System.out.println();
			}
		}
		
		
	}
	
	/**
	 * An explicit integer encoding of nqueens
	 * @author Emina Torlak
	 */
	private static class IntQueens extends NQueens {
		private final Relation queen, x, y;
		private final int n;
		/**
		 * Constructs an nqueens instance for the given n.
		 */
		IntQueens(int n) { 
			assert n > 0;
			this.n = n;
			this.queen = Relation.unary("Queen");
			this.x = Relation.binary("x");
			this.y = Relation.binary("y");
		}
		
		/**
		 * Returns an explicit integer encoding of the problem.
		 * @return an explicit integer encoding of the problem.
		 */
		public Formula rules() {
			final List<Formula> rules = new ArrayList<Formula>();
			
			rules.add(x.function(queen, Expression.INTS));
			rules.add(y.function(queen, Expression.INTS));
			
			final Variable i = Variable.unary("n");
			// at most one queen in each row: all i: INTS | lone x.i
			
			rules.add(x.join(i).lone().forAll(i.oneOf(Expression.INTS)));
			
			// at most one queen in each column: all i: INTS | lone y.i
			rules.add(y.join(i).lone().forAll(i.oneOf(Expression.INTS)));

			final Variable q1 = Variable.unary("q1"), q2 = Variable.unary("q2");
						
			// at most one queen on each diagonal :
			// all q1: Queen, q2: Queen - q1 | abs[bitOr[q2.x] - bitOr[q1.x]] != abs[bitOr[q2.y] - bitOr[q1.y]]
			
			final IntExpression xAbsDiff = q2.join(x).sum().minus(q1.join(x).sum()).abs();
			final IntExpression yAbsDiff = q2.join(y).sum().minus(q1.join(y).sum()).abs();
					
			rules.add(xAbsDiff.eq(yAbsDiff).not().forAll(q1.oneOf(queen).and(q2.oneOf(queen.difference(q1)))));
		
			return Formula.and(rules);
		}
		
		/**
		 * Returns a bounds for the explicit integer encoding.
		 * @requires n > 0
		 * @return bounds for the explicit integer encoding.
		 */
		public Bounds bounds() { 
			
			final List<Integer> atoms = new ArrayList<Integer>(n);
			for(int i =0; i < n; i++) { 
				atoms.add(Integer.valueOf(i));
			}
			
			final Universe u = new Universe(atoms);
			final Bounds b = new Bounds(u);
			final TupleFactory f = u.factory();
			
			b.boundExactly(queen, f.allOf(1));
			b.bound(x, f.allOf(2));
			b.bound(y, f.allOf(2));
			
			for(int i = 0; i < n; i++) { 
				b.boundExactly(i, f.setOf(Integer.valueOf(i)));
			}
			
			return b;
		}
		
		/**
		 * Prints the given solution
		 */
		void print(Instance instance, Options options) { 
			final Evaluator eval = new Evaluator(instance, options);
			for(int i = 0; i < n; i++) { 
				Expression ci = IntConstant.constant(i).toExpression();
				for(int j = 0; j < n; j++) { 
					Expression cj = IntConstant.constant(j).toExpression();
					if (eval.evaluate(x.join(ci).intersection(y.join(cj)).some())) { 
						System.out.print(" Q");
					} else {
						System.out.print(" .");
					}
				}
				System.out.println();
			}
		}
		
	}
}
