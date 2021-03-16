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

import java.util.Iterator;
import java.util.NoSuchElementException;

import kodkod.util.ints.Ints;

/**
 * A logic NOT gate.
 *
 * @invariant this.op = Operator.NOT
 * @invariant #inputs = 1
 * @invariant this.label = -inputs.label
 * @invariant label in (-Integer.MAX_VALUE..-1]
 * @author Emina Torlak
 */
public final class NotGate extends BooleanFormula {

    private final int hashcode;

    /**
     * Constructs a new NotGate with the given formula as its input.
     *
     * @requires input != null && input !in NotGate
     * @ensures this.inputs' = 0->input && this.output'.label = -input.label
     */
    NotGate(BooleanFormula input) {
        super(input);
        this.hashcode = Ints.superFastHash(-input.label());
    }

    /**
     * Returns a hash of this inverter's label.
     *
     * @return Ints.superFastHash(this.label)
     */
    @Override
    int hash(Operator op) {
        return hashcode;
    }

    /**
     * Returns an iterator that returns this gate's single input.
     *
     * @return an iterator over this.inputs.
     */
    @Override
    public Iterator<BooleanFormula> iterator() {
        return new Iterator<BooleanFormula>() {

            boolean hasNext = true;

            @Override
            public boolean hasNext() {
                return hasNext;
            }

            @Override
            public BooleanFormula next() {
                if (!hasNext)
                    throw new NoSuchElementException();
                hasNext = false;
                return negation();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }

    /**
     * Returns the label for this value.
     *
     * @return this.label
     */
    @Override
    public final int label() {
        return -negation().label();
    }

    /**
     * Returns 1.
     *
     * @return 1.
     */
    @Override
    public int size() {
        return 1;
    }

    /**
     * Passes this value and the given argument value to the visitor, and returns
     * the resulting value.
     *
     * @return the value produced by the visitor when visiting this node with the
     *         given argument.
     */
    @Override
    public <T, A> T accept(BooleanVisitor<T,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    /**
     * Returns a string representation of this inverter.
     *
     * @return a string representation of this inverter.
     */
    @Override
    public String toString() {
        return "!" + negation().toString();
    }

    /**
     * Returns Operator.NOT.
     *
     * @return Operator.NOT
     */
    @Override
    public kodkod.engine.bool.Operator op() {
        return kodkod.engine.bool.Operator.NOT;
    }

    /**
     * Returns this.input[i].
     *
     * @return this.input[i]
     * @throws IndexOutOfBoundsException i != 0
     */
    @Override
    public BooleanFormula input(int i) {
        if (i != 0)
            throw new IndexOutOfBoundsException();
        return negation();
    }

    /**
     * Returns a hashcode for this inverter.
     *
     * @return a hashcode for this inverter.
     */
    @Override
    public int hashCode() {
        return hashcode;
    }
}
