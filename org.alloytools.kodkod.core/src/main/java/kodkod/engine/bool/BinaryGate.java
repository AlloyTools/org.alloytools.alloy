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
import java.util.Set;

/**
 * A logic gate with two inputs.
 *
 * @invariant #this.inputs = 2
 * @invariant digest = sum(inputs.digest(this.op))
 */
final class BinaryGate extends MultiGate {

    private final BooleanFormula low, high;

    /**
     * Constructs a new binary gate with the given operator, label, and inputs.
     *
     * @requires components.h = components.l && l.label < h.label
     * @ensures this.op' = op && this.inputs' = l + h && this.label' = label
     */
    BinaryGate(Operator.Nary op, int label, int hashcode, BooleanFormula l, BooleanFormula h) {
        super(op, label, hashcode);
        assert l.label() < h.label();
        this.low = l;
        this.high = h;
    }

    /**
     * Returns an integer k' such that 0 < |k'| < k and |k'| is the number of
     * flattening steps that need to be taken to determine that this circuit has (or
     * does not have) an input with the given label. A positive k' indicates that f
     * is found to be an input to this circuit in k' steps. A negative k' indicates
     * that f is not an input to this circuit, when it is flattened using at most k
     * steps.
     *
     * @requires k > 0
     * @return the number of flattening steps that need to be taken to determine
     *         that f is (not) an input to this circuit
     */
    @Override
    int contains(Operator op, int f, int k) {
        assert k > 0;
        if (f == label())
            return 1;
        else if (this.op != op || k < 2 || f > label() || -f > label())
            return -1;
        else {
            final int l = low.contains(op, f, k - 1);
            if (l > 0)
                return l;
            else {
                final int h = high.contains(op, f, k - l);
                return h > 0 ? h - l : h + l;
            }
        }
    }

    /**
     * Flattens this circuit with respect to the given operator into the provided
     * set. Specifically, the method modifies the set so that it contains the
     * elements f_0, ..., f_k' where k' <= k elements and [[this]] = op(f_0, ...,
     * f_k'). The default implementation simply adds this to the set.
     *
     * @requires k > 0
     * @ensures 1 <= k' <= k && some f_0,..., f_k' : flat.elts' | [[this]] =
     *          op([[f_0]], ..., [[f_k']])
     */
    @Override
    void flatten(Operator op, Set<BooleanFormula> flat, int k) {
        assert k > 0;
        if (this.op == op && k > 1) {
            final int oldsize = flat.size();
            low.flatten(op, flat, k - 1);
            high.flatten(op, flat, k - (flat.size() - oldsize));
        } else {
            flat.add(this);
        }
    }

    /**
     * Returns 2.
     *
     * @return 2
     */
    @Override
    public int size() {
        return 2;
    }

    /**
     * Returns an iterator over the inputs to this gate, in the increasing label
     * order.
     *
     * @return an iterator over this.inputs.
     */
    @Override
    public Iterator<BooleanFormula> iterator() {
        return new Iterator<BooleanFormula>() {

            int next = 0;

            @Override
            public boolean hasNext() {
                return next < 2;
            }

            @Override
            public BooleanFormula next() {
                if (!hasNext())
                    throw new NoSuchElementException();
                return (next++ == 0 ? low : high);
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * Returns the ith input to this gate.
     *
     * @return this.inputs[i]
     * @requires 0 <= i < size
     * @throws IndexOutOfBoundsException i < 0 || i >= #this.inputs
     */
    @Override
    public BooleanFormula input(int i) {
        switch (i) {
            case 0 :
                return low;
            case 1 :
                return high;
            default :
                throw new IndexOutOfBoundsException();
        }
    }
}
