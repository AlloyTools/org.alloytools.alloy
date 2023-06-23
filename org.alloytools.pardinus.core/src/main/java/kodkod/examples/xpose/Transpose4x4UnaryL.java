/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.examples.xpose;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A Kodkod "unary" encoding of the Transpose4x4 synthesis problem with 
 * holes on the left hand side.
 *  
 * @author Emina Torlak
 */
public final class Transpose4x4UnaryL {
	final Relation[] mx1 = new Relation[4], mx2 = new Relation[4];
	final Relation[] sx1 = new Relation[4], sx2 = new Relation[4];
	final Relation[][] mi = new Relation[4][4], si = new Relation[4][4];
	final Relation succ;
	static final Expression[] ints = new Expression[16];
	
	public Transpose4x4UnaryL() {
		for(int i = 0; i < 4; i++) {
			mx1[i] = Relation.unary("mx1[" + i + "]");
			mx2[i] = Relation.unary("mx2[" + i + "]");			
			sx1[i] = Relation.unary("sx1[" + i + "]");
			sx2[i] = Relation.unary("sx2[" + i + "]");
			for(int j = 0; j < 4; j++) {
				mi[i][j] = Relation.unary("mi[" + i + ", " + j + "]");
				si[i][j] = Relation.unary("si[" + i + ", " + j + "]");
			}
		}
		this.succ = Relation.binary("succ");	
		for(int i = 0; i < 16; i++) {
			ints[i] = IntConstant.constant(i).toExpression();
		}
		
	}
	
	/**
	 * Representation invariants which ensure that every relation
	 * representing a hole is a singleton.
	 * @return an encoding of representation invariants
	 */
	final Formula invariants() {
		final List<Formula> inv = new ArrayList<Formula>(32);
		for(int i = 0; i < 4; i++) {
			inv.add(mx1[i].one());
			inv.add(mx2[i].one());		
			inv.add(sx1[i].one());
			inv.add(sx2[i].one());
			for(int j = 0; j < 4; j++) {
				inv.add(mi[i][j].one());
				inv.add(si[i][j].one());
			}
		}
		return Formula.and(	inv );
	}
	
	/**
	 * Returns an expression that represents the transpose of m, as implemented by the {@link Transpose4x4#transposeShufps(int[]) } method.
	 * @return an expression that represents the transpose of m, as implemented by the {@link Transpose4x4#transposeShufps(int[]) } method.
	 */
	final Expression transposeShufps(Expression m) {
		final Expression s = Expression.UNIV.product(ints[0]); // s = new int[16];
		final Expression t = Expression.UNIV.product(ints[0]); // t = new int[16];	
			
		final Expression s0 = wr4(s,  shufps(rd4(m, mx1[0]), rd4(m, mx2[0]), mi[0]),  0);		// s0
		final Expression s1 = wr4(s0, shufps(rd4(m, mx1[1]), rd4(m, mx2[1]), mi[1]),  4);   	// s1
		final Expression s2 = wr4(s1, shufps(rd4(m, mx1[2]), rd4(m, mx2[2]), mi[2]),  8);   	// s2
		final Expression s3 = wr4(s2, shufps(rd4(m, mx1[3]), rd4(m, mx2[3]), mi[3]), 12);   	// s3
		
		final Expression t0 = wr4(t,  shufps(rd4(s3, sx1[0]), rd4(s3, sx2[0]), si[0]),  0);  	// t0
		final Expression t1 = wr4(t0, shufps(rd4(s3, sx1[1]), rd4(s3, sx2[1]), si[1]),  4);  	// t1
		final Expression t2 = wr4(t1, shufps(rd4(s3, sx1[2]), rd4(s3, sx2[2]), si[2]),  8);  	// t2
		final Expression t3 = wr4(t2, shufps(rd4(s3, sx1[3]), rd4(s3, sx2[3]), si[3]), 12);  	// t3
		
		return t3;
	}
	
	
	/**
	 * Encodes the shufps SIMD instruction.
	 * @requires xmm1.arity = 2 and xmm2.arity = 2 and imm8.length = 4 
	 * @requires all i: [0..3] | imm8[i].arity = 1
	 * @return 0->xmm1[imm8[0]] + 1->xmm1[imm8[1]] + 2->xmm2[imm8[2]] + 3->xmm2[imm8[3]]
	 */
	final Expression shufps(Expression xmm1, Expression xmm2, Expression[] imm8) {
		return Expression.union(ints[0].product(get(xmm1, imm8[0])), 
								ints[1].product(get(xmm1, imm8[1])), 
								ints[2].product(get(xmm2, imm8[2])), 
								ints[3].product(get(xmm2, imm8[3])));
	}
	
	/**
	 * Encodes the result of reading a subarray of length 4 from the given array, starting at the given index.
	 * @requires m.arity = 2 and pos.arity = 1
	 * @return 0->m[pos] + 1->m[pos+1] + 2->[pos+2] + 3->[pos+3]
	 */
	final Expression rd4(Expression m, Expression pos) {
		return Expression.union(ints[0].product(get(m, pos)), 
								ints[1].product(get(m, add(pos, 1))), 
								ints[2].product(get(m, add(pos, 2))), 
								ints[3].product(get(m, add(pos, 3))));
	}
	
	/**
	 * Encodes the result of writing the four elements from the source into the destination array at the specified position.
	 * @requires dst.arity = 2 and pos.arity = 1 and src.arity = 2
	 * @return old(dst) ++ (pos->src[0] + (pos+1)->src[1] + (pos+2)->src[2] + (pos+3)->src[3])
	 */
	final Expression wr4(Expression dst, Expression src, int pos) {
		return dst.override(Expression.union(	ints[pos].product(get(src, ints[0])), 
												ints[pos + 1].product(get(src, ints[1])), 
												ints[pos + 2].product(get(src, ints[2])), 
												ints[pos + 3].product(get(src, ints[3])) ));
	}
	
	/**
	 * Returns an encoding of sequence lookup using relational join, where
	 * seq is a sequence (binary relation from integers to values) and idx is an integer.
	 * @return seq[idx]
	 */
	final Expression get(Expression seq, Expression idx) { 
		return idx.join(seq);								 
	}
	
	/**
	 * Returns an encoding of array update using relational override, where
	 * seq is a sequence (binary relation from integers to values), idx is an integer, and 
	 * val is the new value for seq at idx.
	 * @return seq ++ (idx -> val)
	 */
	final Expression set(Expression seq, Expression idx, Expression val) {
		return seq.override(idx.product(val));
	}
	
	/**
	 * Returns the result of adding the non-negative given constant to the given index.
	 * @requires idx.arity = 1 and k >= 0
	 * @return idx + k
	 */
	final Expression add(Expression idx, int k) {
		Expression ret = idx;
		for(int i = 0; i < k; i++) {
			ret = get(succ, ret);
		}
		return ret;
	}
	
	/**
	 * Returns relation bounds over a universe of interpretation consisting of integers 0 - 15, inclusive.
	 * @return relation bounds over a universe of interpretation consisting of integers 0 - 15, inclusive.
	 */
	final Bounds bounds() {
		final Universe u = new Universe(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
		final TupleFactory f = u.factory();
		
		final Bounds b = new Bounds(u);
		
		// tell the solver to interpret integer objects as their corresponding integer values
		for (int i = 0; i < 16; i++)
			b.boundExactly(i, f.setOf(i));
		
		final TupleSet s3 = f.setOf(0, 1, 2, 3);        										// { 0, 1, 2, 3 }
		final TupleSet s12 = f.setOf(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12); 	// { 0, ..., 12 }
		for(int i = 0; i < 4; i++) {
			b.bound(mx1[i], s12);
			b.bound(mx2[i], s12);		
			b.bound(sx1[i], s12);
			b.bound(sx2[i], s12);
			for(int j = 0; j < 4; j++) {
				b.bound(mi[i][j], s3);
				b.bound(si[i][j], s3);
			}
		}
		
		final TupleSet ord = f.noneOf(2);  				// { [0, 1], [1, 2], [2, 3], ..., [14, 15] }
		for(int i = 0; i < 15; i++)
			ord.add(f.tuple((Object)i, i+1));
		b.boundExactly(succ, ord);
		
		return b;
	}
	
	/**
	 * Returns the options used for solving.
	 * @return options used for solving.
	 */
	final Options options() {
		final Options opt = new Options();
		opt.setSolver(SATFactory.MiniSat);
		opt.setBitwidth(5);
		return opt;
	}
	/**
	 * Synthesizes selector and mask values for the given input, using {@link Transpose4x4#transpose(int[])}
	 * as the spec.
	 * @requires m.length = 16 && (all i: [0..15] | 0 <= m[i] <= 15)
	 * @return a solution for relations mx1, mx2, mi, sx1, sx2, and si
	 */
	final Solution solve(int[] m) {
		final Solver s = new Solver(options());
		return s.solve(invariants().and(toExpr(Transpose4x4.transpose(m)).eq(transposeShufps(toExpr(m)))), bounds());
	}
	
	/**
	 * Converts the given integer array to a binary relation representation. 
	 * @return 0->val[0] + 1->val[1] + ... + (val.length-1)->val[val.length-1]
	 */
	final static Expression toExpr(int[] val) {
		final Expression[] exprs = new Expression[val.length];
		for(int i = 0; i < val.length; i++)
			exprs[i] = ints[i].product(ints[val[i]]);
		return Expression.union(exprs);
	}
	
	/** Converts the given tupleset to an array of ints. */
	private final static int[] toArray(TupleSet a) {
		assert a.arity() == 2;
		final int[] ret = new int[a.size()];
		final Iterator<Tuple> itr = a.iterator();
		for(int i = 0; i < ret.length; i++) {
			final Tuple t = itr.next();
			assert t.atom(0).equals(i);
			ret[i] = (Integer) t.atom(1);
		}
		return ret;
	}
	
	/** Converts the given array of singleton integer relations to an array of ints. */
	private final static int[] toArray(Evaluator eval, Expression... r) {
		final int[] ret = new int[r.length];
		for(int i = 0; i < r.length; i++) {
			final TupleSet ts = eval.evaluate(r[i]);
			assert ts.arity() == 1 && ts.size() == 1;
			ret[i] = (Integer) ts.iterator().next().atom(0);
		}
		return ret;
	}
	
	/** Converts the given array of singleton integer relations to an array of ints. */
	private final static int[][] toArray2D(Evaluator eval, Expression[][] r) {
		final int[][] ret = new int[r.length][];
		for(int i = 0; i < r.length; i++) {
			ret[i] = toArray(eval, r[i]);
		}
		return ret;
	}
	
	public static void main(String[] args) {
		final int[] a = new int[] { 0,  1,  2,  3, 
				                    4,  5,  6,  7,
				                    8,  9, 10, 11,
				                   12, 13, 14, 15}; // 4.5 sec
		final int[] b = new int[] { 0,  4,  8, 12, 
					                1,  5,  9, 13,
					                2,  6, 10, 14,
					                3,  7, 11, 15}; // 6.4 sec
		final int[] c = new int[] {  4, 15,  2,  9, 
	            						12, 13, 11,  8, 
	            						14,  6,  0,  3, 
	            						5,  7, 10,  1}; // 1.6 sec
		final int[] d = new int[] { 9, 12, 11,  2, 
	             					8,  6, 13, 15, 
	             					4,  1,  7, 14, 
	             					5, 10,  0,  3 }; // 3 sec
		final int[] e = new int[] {  2,  9,  5, 11,
						            15,  4,  3,  6, 
						            13, 10,  1, 14,  
						             0, 12,  8,  7}; // 2 sec
		
		final Transpose4x4UnaryL enc = new Transpose4x4UnaryL();
		final Solution sol = enc.solve(a);
		System.out.println(sol);
		if (sol.instance()==null) {
			return;
		}
		
		final Evaluator eval = new Evaluator(sol.instance(), enc.options());
		
		System.out.println("\nmx1 = " + Arrays.toString(toArray(eval, enc.mx1)));
		System.out.println("mx2 = " + Arrays.toString(toArray(eval, enc.mx2)));
		System.out.println("mi  = " + Arrays.deepToString(toArray2D(eval, enc.mi)));
		System.out.println("sx1 = " + Arrays.toString(toArray(eval, enc.sx1)));
		System.out.println("sx2 = " + Arrays.toString(toArray(eval, enc.sx2)));
		System.out.println("si  = " + Arrays.deepToString(toArray2D(eval, enc.si)));
		
		for(int[] in : new int[][] {a, b, c, d, e}) {
			System.out.println("\na                  = " + Arrays.toString(in));
			final int[] expected = Transpose4x4.transpose(in);
			final int[] evalTS = toArray(eval.evaluate(enc.transposeShufps(toExpr(in))));
			System.out.println("expected(a)        = " + Arrays.toString(expected));			
			System.out.println("transposeShufps(a) = " + Arrays.toString(evalTS));
			assert Arrays.equals(expected, evalTS);
		}
		
	}
}
