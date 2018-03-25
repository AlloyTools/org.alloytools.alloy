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
 * Enumerates unary (~, ^, *), binary (+, &, ++, ->, -, .) and nary (+, &, ++,
 * ->) expression operators.
 *
 * @specfield op: (int->lone Expression) -> Expression
 * @invariant all args: seq Expression, out: Expression | args->out in op =>
 *            (out.children = args && out.op = this)
 */
public enum ExprOperator {
                          /** Relational union (+) operator. */
                          UNION {

                              @Override
                              public String toString() {
                                  return "+";
                              }
                          },
                          /** Relational intersection (&) operator. */
                          INTERSECTION {

                              @Override
                              public String toString() {
                                  return "&";
                              }
                          },
                          /** Relational override (++) operator. */
                          OVERRIDE {

                              @Override
                              public String toString() {
                                  return "++";
                              }
                          },
                          /** Relational product (->) operator. */
                          PRODUCT {

                              @Override
                              public String toString() {
                                  return "->";
                              }
                          },
                          /** Relational difference (-) operator. */
                          DIFFERENCE {

                              @Override
                              public String toString() {
                                  return "-";
                              }
                          },
                          /** Relational join (.) operator. */
                          JOIN {

                              @Override
                              public String toString() {
                                  return ".";
                              }
                          },
                          /** Transpose (~) operator. */
                          TRANSPOSE {

                              @Override
                              public String toString() {
                                  return "~";
                              }
                          },
                          /** Transitive closure (^) operator. */
                          CLOSURE {

                              @Override
                              public String toString() {
                                  return "^";
                              }
                          },
                          /** Reflexive transitive closure (*) operator. */
                          REFLEXIVE_CLOSURE {

                              @Override
                              public String toString() {
                                  return "*";
                              }
                          },
                          /**
                           * Value in post-state (used only for fixpoint computation.
                           */
                          PRE {

                              @Override
                              public String toString() {
                                  return "PRE";
                              }
                          };

    static final int unary  = TRANSPOSE.index() | CLOSURE.index() | REFLEXIVE_CLOSURE.index() | PRE.index();

    static final int binary = ~unary;

    static final int nary   = UNION.index() | INTERSECTION.index() | OVERRIDE.index() | PRODUCT.index();

    private final int index() {
        return 1 << ordinal();
    }

    /**
     * Returns true if this is a unary operator.
     *
     * @return true if this is a unary operator.
     */
    public final boolean unary() {
        return (unary & index()) != 0;
    }

    /**
     * Returns true if this is a binary operator.
     *
     * @return true if this is a binary operator.
     */
    public final boolean binary() {
        return (binary & index()) != 0;
    }

    /**
     * Returns true if this is an nary operator.
     *
     * @return true if this is an nary operator.
     */
    public final boolean nary() {
        return (nary & index()) != 0;
    }

}
