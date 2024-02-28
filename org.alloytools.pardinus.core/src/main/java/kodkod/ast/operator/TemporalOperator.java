/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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
 * Enumerates unary (always, eventually, next, historically, once, previous, ') and 
 * binary (release, until) temporal operators. 
 * @specfield op: (int->lone Formula) -> Formula
 * @invariant all args: seq Formula, out: Formula | args->out in op => (out.children = args && out.op = this)
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public enum TemporalOperator {
    /** Next unary temporal operator. */
    AFTER 			{ public String toString() { return "after"; }},
    /** Always unary temporal operator. */
    ALWAYS  		{ public String toString() { return "always"; }},
    /** Eventually unary temporal operator. */
    EVENTUALLY 		{ public String toString() { return "eventually"; }},
    /** Previous unary temporal operator. */
    BEFORE			{ public String toString() { return "before"; }},
    /** Historically unary temporal operator. */
    HISTORICALLY  	{ public String toString() { return "historically"; }},
    /** Once unary temporal operator. */
    ONCE 			{ public String toString() { return "once"; }},
    /** Until binary temporal operator. */
    UNTIL 			{ public String toString() { return "until"; }},
    /** Release binary temporal operator. */
    RELEASES 		{ public String toString() { return "releases"; }},
    /** Since binary temporal operator. */
    SINCE 			{ public String toString() { return "since"; }},
    /** Trigger binary temporal operator. */
    TRIGGERED 		{ public String toString() { return "triggered"; }},
    /** Priming temporal operator. */
    PRIME 			{ public String toString() { return "'";} };
  	
    static final int binary = UNTIL.index() | RELEASES.index() | SINCE.index() | TRIGGERED.index();

    static final int unary = ~binary;

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
    
}