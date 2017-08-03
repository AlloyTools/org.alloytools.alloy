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
package kodkod.ast.operator;



/**
 * Enumerate unary (-, ~, abs, sgn), binary (+, *, &, |, -, /, %, >>, >>>, <<) and nary (+, *, &, |) operators on integer expressions.
 * @specfield op: (int->lone IntExpression) -> IntExpression
 * @invariant all args: seq IntExpression, out: IntExpression | args->out in op => (out.children = args && out.op = this)
 */
public enum IntOperator {
	/** `+' operator */
	PLUS 		{ public String toString() { return "+"; } },
	/** `*' operator */
	MULTIPLY 	{ public String toString() { return "*"; } }, 
	/** `-' operator */
	MINUS 		{ public String toString() { return "-"; } },
	/** `/' operator */
	DIVIDE 		{ public String toString() { return "/"; } },
	/** `%' operator */
	MODULO 		{ public String toString() { return "%"; } },
	/** Bitwise AND operator */
	AND 		{ public String toString() { return "&"; } },
	/** Bitwise OR operator */
	OR 			{ public String toString() { return "|"; } }, 
	/** Bitwise XOR operator */
	XOR 		{ public String toString() { return "^"; } }, 
	/** Left shift operator */
	SHL 		{ public String toString() { return "<<"; } }, 
	/** Right shift operator with zero extension */
	SHR 		{ public String toString() { return ">>>"; } }, 
	/** Right shift operator with sign extension */
	SHA 		{ public String toString() { return ">>"; } },
	/** unary negation (`-') operator */
	NEG 		{ public String toString() { return "-"; } },
	/** bit negation (`~') operator */
	NOT 		{ public String toString() { return "~"; } }, 
	/** absolute value function */
	ABS 		{ public String toString() { return "abs";} }, 
	/** signum function */
	SGN 		{ public String toString() { return "sgn"; } };

	static final int unary = NEG.index() | NOT.index() | ABS.index() | SGN.index();
	
	static final int binary = ~unary;
	
	static final int nary = PLUS.index() | MULTIPLY.index() | AND.index() | OR.index();
	
	private final int index() { return 1<<ordinal(); }
	
	/**
     * Returns true if this is a unary operator.
     * @return true if this is a unary operator.
     */
    public final boolean unary() { return (unary & index())!=0; }
    
    /**
     * Returns true if this is a binary operator.
     * @return true if this is a binary operator.
     */
    public final boolean binary() { return (binary & index())!=0; }
    
    /**
     * Returns true if this is an nary operator.
     * @return true if this is an nary operator.
     */
    public final boolean nary() { return (nary & index())!=0; }
}