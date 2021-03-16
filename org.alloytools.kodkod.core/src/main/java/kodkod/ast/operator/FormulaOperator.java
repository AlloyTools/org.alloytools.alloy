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
 * Enumerates binary (&&, ||, =>, <=>) and nary (&&, ||) logical operators.
 *
 * @specfield op: (int->lone Formula) -> Formula
 * @invariant all args: seq Formula, out: Formula | args->out in op =>
 *            (out.children = args && out.op = this)
 */
public enum FormulaOperator {
                             /** Logical AND operator. */
                             AND {

                                 @Override
                                 public String toString() {
                                     return "&&";
                                 }
                             },
                             /** Logical OR operator. */
                             OR {

                                 @Override
                                 public String toString() {
                                     return "||";
                                 }
                             },
                             /** Logical bi-implication operator. */
                             IFF {

                                 @Override
                                 public String toString() {
                                     return "<=>";
                                 }
                             },
                             /** Logical implication operator. */
                             IMPLIES {

                                 @Override
                                 public String toString() {
                                     return "=>";
                                 }
                             };

    static final int nary = (1 << AND.ordinal()) | (1 << OR.ordinal());

    /**
     * Returns true if this is an nary operator.
     *
     * @return true if this is an nary operator
     */
    public final boolean nary() {
        return (nary & (1 << ordinal())) != 0;
    }

}
