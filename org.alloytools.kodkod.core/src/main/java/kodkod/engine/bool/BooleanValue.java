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
 * Represents a boolean value, which may be a
 * {@link kodkod.engine.bool.BooleanFormula formula} or a
 * {@link kodkod.engine.bool.BooleanConstant constant}. Boolean formulas are
 * produced by {@link kodkod.engine.bool.BooleanFactory circuit factories}. Each
 * value is associated with an integer label; the labels are unique within a
 * given factory. A boolean value with a negative label -|l| represents the
 * negation of the value with the positive label |l|. Non-constant values are
 * not shared among factories.
 *
 * @specfield op: Operator
 * @specfield label: [-Integer.MAX_VALUE, Integer.MAX_VALUE]
 * @invariant no c: BooleanValue - this | some components.c & components.this &&
 *            c.label = this.label
 * @author Emina Torlak
 */
public abstract class BooleanValue implements Comparable<BooleanValue> {

    BooleanValue() {}

    /**
     * Returns the negation of this boolean value
     *
     * @return { f: BooleanFormula | [[f]] = ![[this]] }
     */
    abstract BooleanValue negation();

    /**
     * Returns the label for this value.
     *
     * @return this.label
     */
    public abstract int label();

    /**
     * Returns the operator representing the function computed by this gate.
     *
     * @return this.op
     */
    public abstract Operator op();

    /**
     * Boolean components are ordered according to their labels. Note that the
     * ordering is well defined on components produced by the same factory.
     * Specifically, this comparison function is consistent with equals for the
     * components produced by the same factory, but may not be for the components
     * produced by different factories.
     *
     * @return 0 if the label of this and other are the same, a negative integer if
     *         the label of this is smaller than the label of other; and a positive
     *         integer otherwise.
     */
    @Override
    public final int compareTo(BooleanValue other) {
        return label() - other.label();
    }
}
