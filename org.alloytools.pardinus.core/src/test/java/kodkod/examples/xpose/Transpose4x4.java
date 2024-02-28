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


import java.util.Arrays;
/**
 * Implements the transpose of a 4x4 matrix with shufps.
 * 
 * @author Emina Torlak
 */
public final class Transpose4x4 {
	// these are the values that we will be synthesizing
	private static final int[]  mx1 = new int[] {  9, 1,  4, 0 };
	private static final int[]  mx2 = new int[] { 12, 5, 10, 6 };
	private static final int[][] mi = new int[][] { {1, 2, 2, 3}, {0, 2, 0, 3}, {3, 0, 2, 3}, {0, 2, 3, 0} }; 
	private static final int[]  sx1 = new int[] { 9,  4, 12, 5 };
	private static final int[]  sx2 = new int[] { 7, 11,  0, 0 };
	private static final int[][] si = new int[][] { {3, 0, 0, 3}, {0, 2, 3, 0}, {1, 3, 0, 2}, {0, 3, 1, 3} }; 

	/**
	 * Transposes a 4x4 matrix m given as an array of 16 values.
	 * @requires m.length = 16
	 * @return some t: int[] | 
	 *          t.length = 16 and
	 *          all i, j: [0..4] | t[4*i + j] = m[4*j + i]
	 */
	public static final int[] transpose(int[] m) {
		assert m.length == 16;
		final int[] t = new int[16];
		for (int i = 0; i < 4; i++)
		    for (int j = 0; j < 4; j++)
		      t[4 * i + j] = m[4 * j + i];
		return t;
	}
	
	/**
	 * Transposes a 4x4 matrix m given as an array of 16 values, using 
	 * the shufps instruction.
	 * @requires m.length = 16
	 * @return some t: int[] | 
	 *          t.length = 16 and
	 *          all i, j: [0..4] | t[4*i + j] = m[4*j + i]
	 */
	public static final int[] transposeShufps(int[] m) {
		assert m.length == 16;
		final int[] s = new int[16];
		final int[] t = new int[16];
			
		write4(s, 0, shufps(read4(m, mx1[0]), read4(m, mx2[0]), mi[0]));  // s0
		write4(s, 4, shufps(read4(m, mx1[1]), read4(m, mx2[1]), mi[1]));  // s1
		write4(s, 8, shufps(read4(m, mx1[2]), read4(m, mx2[2]), mi[2]));  // s2
		write4(s, 12, shufps(read4(m, mx1[3]), read4(m, mx2[3]), mi[3])); // s3
		
		write4(t, 0, shufps(read4(s, sx1[0]), read4(s, sx2[0]), si[0]));  // t0
		write4(t, 4, shufps(read4(s, sx1[1]), read4(s, sx2[1]), si[1]));  // t1
		write4(t, 8, shufps(read4(s, sx1[2]), read4(s, sx2[2]), si[2]));  // t2
		write4(t, 12, shufps(read4(s, sx1[3]), read4(s, sx2[3]), si[3])); // t3
		
		assert Arrays.equals(t, transpose(m));
		
		return t;
	}
	
	/**
	 * Simulates the shufps SIMD instruction.
	 * @requires xmm1.length = 4 and xmm2.length = 4 and imm8.length = 4
	 * @requires all i: [0..3] | 0 <= imm8[i] < 4
	 * @return 0->xmm1[imm8[0]] + 1->xmm1[imm8[1]] + 2->xmm2[imm8[2]] + 3->xmm2[imm8[3]]
	 */
	static final int[] shufps(int[] xmm1, int[] xmm2, int[] imm8) {
		return new int[] { xmm1[imm8[0]], xmm1[imm8[1]], xmm2[imm8[2]], xmm2[imm8[3]] };
	}
	
	/**
	 * Reads a subarray of length 4 from the given array, starting 
	 * at the given index.
	 * @requires m.length >= 4
	 * @requires pos >= 0 and pos + 4 <= m.length
	 * @return 0->m[pos] + 1->m[pos+1] + 2->[pos+2] + 3->[pos+3]
	 */
	static final int[] read4(int[] m, int pos) {
		assert m.length >= 4;
		assert pos >= 0 && pos + 4 <= m.length;
		return new int[] { m[pos], m[pos + 1], m[pos + 2], m[pos + 3] };
	}
	
	/**
	 * Writes the four elements from the source into the destination array at the specified position.
	 * @requires src.length = 4 and dst.length >= 4
	 * @requires 0 <= pos <= dst.length - 4
	 * @ensures dst = old(dst) ++ (pos->src[0] + (pos+1)->src[1] + (pos+2)->src[2] + (pos+3)->src[3])
	 */
	static final void write4(int[] dst, int pos, int[] src) {
		dst[pos] = src[0];
		dst[pos+1] = src[1];
		dst[pos+2] = src[2];
		dst[pos+3] = src[3];
	}
	
	public static void main(String[] args) {
		final int[] a = new int[] { 0,  1,  2,  3, 
				                    4,  5,  6,  7,
				                    8,  9, 10, 11,
				                   12, 13, 14, 15};
		System.out.println("a = " + Arrays.toString(a));
		System.out.println("transpose(a) = " + Arrays.toString(transpose(a)));
		System.out.println("transposeShufps(a) = " + Arrays.toString(transposeShufps(a)));
	}
		
}
