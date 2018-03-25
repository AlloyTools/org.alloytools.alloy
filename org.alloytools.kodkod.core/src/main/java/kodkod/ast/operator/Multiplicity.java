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
 * Represents the multiplicity of an expression in a
 * {@link kodkod.ast.MultiplicityFormula} or the multiplicity of a variable in a
 * {@link kodkod.ast.Decl }.
 *
 * @author Emina Torlak
 */
public enum Multiplicity {
                          /**
                           * <tt>no expr</tt>: expr contains no elements. The 'no' multiplicity can only
                           * be used in a multiplicity formula.
                           */
                          NO {

                              @Override
                              public String toString() {
                                  return "no";
                              }
                          },
                          /**
                           * <tt>lone expr</tt>: expr contains at most one element.
                           */
                          LONE {

                              @Override
                              public String toString() {
                                  return "lone";
                              }
                          },
                          /** <tt>one expr</tt>: expr contains exactly one element. */
                          ONE {

                              @Override
                              public String toString() {
                                  return "one";
                              }
                          },
                          /**
                           * <tt>some expr</tt>: expr contains at least one element.
                           */
                          SOME {

                              @Override
                              public String toString() {
                                  return "some";
                              }
                          },
                          /**
                           * <tt>v: set expr</tt>: v is a subset of expr. The 'set' multiplicity can only
                           * be used in a declaration.
                           */
                          SET {

                              @Override
                              public String toString() {
                                  return "set";
                              }
                          }
}
