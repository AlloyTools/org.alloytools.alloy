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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
 * Relational Kodkod encoding of the BlockedNQueensProblem.
 * The files should be supplied in the same format as those
 * at http://asparagus.cs.uni-potsdam.de/?action=instances&id=15
 * @author Emina Torlak
 */
public final class BlockedNQueens {

	private final Relation queen, x, y, blocked, num, ord;
	private final String file;
	/**
	 * Constructs an instance of BlockedNQueens from the file
	 * with the given name.
	 */
	public BlockedNQueens(final String file) {
		this.file = file;
		this.queen = Relation.unary("Queen");
		this.x = Relation.binary("x");
		this.y = Relation.binary("y");
		this.blocked = Relation.binary("blocked");
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
		final Variable q1 = Variable.unary("q1"), q2 = Variable.unary("q2");
		
		// at most one queen in each row: all i: num | lone x.i
		
		rules.add(x.join(i).lone().forAll(i.oneOf(num)));
		
		// at most one queen in each column: all i: num | lone y.i
		rules.add(y.join(i).lone().forAll(i.oneOf(num)));

		// no queen in a blocked position:  all q: Queen | q.x->q.y !in blocked
		rules.add(q1.join(x).product(q1.join(y)).intersection(blocked).no().forAll(q1.oneOf(queen)));
		
		// at most one queen on each diagonal
		//		all q1: Queen, q2: Queen - q1 |
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
	 * Returns the bounds for relational encoding of the problem based on the input file.
	 * @return the bounds for relational encoding of the problem based on the input file.
	 */
	public Bounds bounds() {
		try(BufferedReader reader = new BufferedReader(new FileReader(new File(file)))) {
			
			
			final Pattern np = Pattern.compile("num\\((\\d+)\\)\\.");
			final Pattern bp = Pattern.compile("block\\((\\d+),\\s*(\\d+)\\)\\.");
			
			String line = "";
			final Matcher m = np.matcher(line);
			
			int n = 0;
			for(line = reader.readLine(); line != null && m.reset(line).matches(); line = reader.readLine()) { 
				n++;
				if (Integer.parseInt(m.group(1))!=n) 
					throw new IOException();
				
			}
						
			if (n==0) throw new IOException();
			
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
		
			// extract the partial instance for the grid
			final TupleSet blocks = f.noneOf(2);
			
			for(m.usePattern(bp); line != null && m.reset(line).matches(); line = reader.readLine()) { 
				Integer i = Integer.parseInt(m.group(1))-1;
				Integer j = Integer.parseInt(m.group(2))-1;
				
				if (i < 0 || i >= n || j < 0 || j >= n)
					throw new IOException();
				
				blocks.add(f.tuple((Object)i, j));
			}
			
			if (line != null) throw new IOException();
			
			b.boundExactly(blocked, blocks);
			
			return b;
			
		} catch (FileNotFoundException e) {
			System.out.println("Could not find " + file);
			usage();
		} catch (IOException e) {
			System.out.println("Badly formatted file: " + file);
			usage();
		} catch (NumberFormatException e) { 
			System.out.println("Badly formatted file: " + file);
			usage();
		} 
		
		return null;
	}
	
	/**
	 * Prints the given solution using the given options to the console
	 */
	void print(Instance instance, Options options) {
		final Evaluator eval = new Evaluator(instance, options);
		final int n = instance.tuples(queen).size();
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
//		System.out.println(instance); 
	}
	
	private static void usage() { 
		System.out.println("Usage:  java BlockedNQueens <file name>");
		System.exit(1);
	}
	
	
	/**
	 * Usage:  java BlockedNQueens <file name>
	 */
	public static void main(String[] args) { 
		
		
		if (args.length < 1)
			usage();
		
	
		try {
						
			final BlockedNQueens model = new BlockedNQueens(args[0]);
			
			final Formula f = model.rules();
			final Bounds b = model.bounds();
			final Solver s = new Solver();
//			System.out.println(b);
			System.out.println(PrettyPrinter.print(f, 1));

			s.options().setSolver(SATFactory.MiniSat);
			s.options().setBitwidth(33 - Integer.numberOfLeadingZeros((b.universe().size()/2) - 1));
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
}
