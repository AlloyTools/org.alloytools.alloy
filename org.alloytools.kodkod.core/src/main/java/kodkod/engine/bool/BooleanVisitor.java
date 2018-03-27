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
package kodkod.engine.bool;

/**
 * Visits {@link kodkod.engine.bool.BooleanFormula boolean formulas}. In
 * addition to passing themselves as the argument to the visitor, the boolean
 * values also pass along satelite information of type A.
 *
 * @author Emina Torlak
 */
public interface BooleanVisitor<T, A> {

    /**
     * Visits the multigate and returns the result.
     *
     * @return the result of visiting the given multigate
     */
    public T visit(MultiGate multigate, A arg);

    /**
     * Visits the if-then-else gate and returns the result.
     *
     * @return the result of visiting the given ITEGate
     */
    public T visit(ITEGate ite, A arg);

    /**
     * Visits the inverter and returns the result.
     *
     * @return the result of visiting the given inverter
     */
    public T visit(NotGate negation, A arg);

    /**
     * Visits the variable and returns the result.
     *
     * @return the result of visiting the given variable
     */
    public T visit(BooleanVariable variable, A arg);

}
