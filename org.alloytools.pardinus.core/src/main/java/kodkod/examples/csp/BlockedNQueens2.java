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
public final class BlockedNQueens2 {

	private final Relation queen, num, ord;
	private final String file;
	/**
	 * Constructs an instance of BlockedNQueens from the file
	 * with the given name.
	 */
	public BlockedNQueens2(final String file) {
		this.file = file;
		this.queen = Relation.binary("Queen");
		this.num = Relation.unary("num");
		this.ord = Relation.binary("ord");
		
	}
	
	/**
	 * Returns a relational encoding of the problem.
	 * @return a relational encoding of the problem.
	 */
	public Formula rules() {
		final List<Formula> rules = new ArrayList<Formula>();
		
		final Variable x = Variable.unary("x"), y = Variable.unary("y");
		// one queen in each row
		rules.add( x.join(queen).one().forAll(x.oneOf(num)) );
		
		// one queen in each column
		rules.add( queen.join(y).one().forAll(y.oneOf(num)) );
		
		// one queen on each diagonal
		final Variable x2 = Variable.unary("p");
		
		
		final Expression ords = ord.closure();
		final Expression y1 = x.join(queen), y2 = x2.join(queen);
		
		final IntExpression xdiff = x.sum().minus(x2.sum()).abs();
		final IntExpression ydiff = y1.sum().minus(y2.sum()).abs();
		
		rules.add( xdiff.eq(ydiff).not().forAll(x.oneOf(num).and(x2.oneOf(ords.join(x))))  );
		
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
			
			final List<Object> atoms = new ArrayList<Object>(n);
		 
			for(int i =0; i < n; i++) { 
				atoms.add(Integer.valueOf(i));
			}
			
			final Universe u = new Universe(atoms);
			final Bounds b = new Bounds(u);
			final TupleFactory f = u.factory();
				
			b.boundExactly(num, f.allOf(1));
						
			final TupleSet obound = f.noneOf(2);
			for(int i = 1; i < n; i++) { 
				obound.add(f.tuple((Object)Integer.valueOf(i-1), Integer.valueOf(i)));
			}
			
			b.boundExactly(ord, obound);
			
			for(int i = 0; i < n; i++) { 
				b.boundExactly(i, f.setOf(Integer.valueOf(i)));
			}
		
			// extract the partial instance for the grid
			final TupleSet qbound = f.noneOf(2);
			
			for(m.usePattern(bp); line != null && m.reset(line).matches(); line = reader.readLine()) { 
				Integer i = Integer.parseInt(m.group(1))-1;
				Integer j = Integer.parseInt(m.group(2))-1;
				
				if (i < 0 || i >= n || j < 0 || j >= n)
					throw new IOException();
					qbound.add(f.tuple((Object)i, j));
			}
			
			if (line != null) throw new IOException();
			
			b.bound(queen, qbound);
			
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
		final int n = instance.universe().size();
		for(int i = 0; i < n; i++) { 
			Expression x = IntConstant.constant(i).toExpression();
			for(int j = 0; j < n; j++) { 
				Expression y = IntConstant.constant(j).toExpression();
				if (eval.evaluate(x.product(y).in(queen))) { 
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
						
			final BlockedNQueens2 model = new BlockedNQueens2(args[0]);
			
			final Formula f = model.rules();
			final Bounds b = model.bounds();
			final Solver s = new Solver();
			System.out.println(b);
			System.out.println(PrettyPrinter.print(f, 1));

			s.options().setSolver(SATFactory.MiniSat);
			s.options().setBitwidth(33 - Integer.numberOfLeadingZeros(b.universe().size()));
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