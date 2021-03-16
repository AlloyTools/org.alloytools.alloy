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

import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * An accumulator for easy construction of gates with multiple inputs. An
 * accumulator cannot be combined with other boolean values using BooleanFactory
 * methods. To use the circuit represented by an accumulator, one must first
 * convert it into a gate by calling
 * {@link BooleanFactory#accumulate(BooleanAccumulator)}.
 *
 * @specfield components: set BooleanValue
 * @specfield op: Operator.Nary
 * @author Emina Torlak
 */
public final class BooleanAccumulator extends BooleanValue implements Iterable<BooleanValue> {

    final Operator.Nary                        op;
    private final SparseSequence<BooleanValue> inputs;
    // private final List<BooleanValue> inputs;

    /**
     * Constructs a new accumulator with the given operator.
     *
     * @requires op != null
     * @ensures this.op' = op && this.label' = label
     */
    private BooleanAccumulator(Operator.Nary op) {
        this.op = op;
        inputs = new TreeSequence<BooleanValue>();
        // inputs = new ArrayList<BooleanValue>();
    }

    /**
     * Returns a tree based implementation of BooleanAccumulator. The addInput
     * operation executes in O(lg n) time where n is the number of gate inputs.
     *
     * @return an empty tree based BooleanAccumulator with the given operator.
     * @throws NullPointerException op = null
     */
    public static BooleanAccumulator treeGate(Operator.Nary op) {
        if (op == null)
            throw new NullPointerException();
        return new BooleanAccumulator(op);
    }

    /**
     * Returns a tree based implementation of BooleanAccumulator, initialized with
     * the given inputs. The addInput operation executes in O(lg n) time where n is
     * the number of gate inputs.
     *
     * @return a tree based BooleanAccumulator with the given operator, initialized
     *         with the given inputs
     * @throws NullPointerException op = null || inputs = null
     */
    public static BooleanAccumulator treeGate(Operator.Nary op, BooleanValue... inputs) {
        if (op == null)
            throw new NullPointerException();
        final BooleanAccumulator ret = new BooleanAccumulator(op);
        for (BooleanValue v : inputs) {
            if (ret.add(v) != ret)
                break;
        }
        return ret;
    }

    /**
     * Returns the operator for this accumulator.
     *
     * @return this.op
     */
    @Override
    public Operator.Nary op() {
        return op;
    }

    /**
     * Adds the given value to this.components and returns the result. Specifically,
     * if the addition of the value causes the gate to evaluate to op.shortCircuit,
     * then this.inputs is set to op.shortCircuit. If the given value has already
     * been added or it is equal to this.op.identity, nothing changes. Otherwise, v
     * is added to this.input. The method returns this.op.shortCircuit if
     * this.inputs contains it after the addition, otherwise it returns the gate
     * itself.
     *
     * @ensures v = this.op.shortCircuit || v.negation in this.components =>
     *          this.components' = this.op.shortCircuit, v !in BooleanConstant =>
     *          this.components' = this.components + v, this.components' =
     *          this.components
     * @return this.components' = op.shortCircuit => op.shortCircuit, this
     */
    public BooleanValue add(BooleanValue v) {
        if (isShortCircuited())
            return op.shortCircuit();
        else {
            final int lit = v.label();
            if (v == op.shortCircuit() || inputs.containsIndex(-lit)) {
                inputs.clear();
                inputs.put(op.shortCircuit().label, op.shortCircuit());
                return op.shortCircuit();
            }
            if (v != op.identity() && !inputs.containsIndex(lit)) {
                inputs.put(lit, v);
            }
            // if (v==op.shortCircuit()) {
            // inputs.clear();
            // inputs.add(op.shortCircuit());
            // return op.shortCircuit();
            // }
            // if (v!=op.identity()) { inputs.add(v); }
            return this;
        }
    }

    /**
     * Returns true if this gate is short circuited; that is, its inputs are reduced
     * to this.op.shortCircuit.
     *
     * @return this.inputs = this.op.shortCircuit
     */
    public boolean isShortCircuited() {
        return inputs.size() == 1 && inputs.first().value() == op.shortCircuit();
        // return inputs.size()==1 && inputs.get(0)==op.shortCircuit();
    }

    /**
     * Throws an IllegalArgumentException if op != this.op, otherwise returns the
     * sum of digests of this gate's inputs with respect to the given operator.
     *
     * @return op = this.op => sum(this.inputs.digest(op))
     * @throws IllegalArgumentException op != this.op
     * @throws ClassCastException some this.inputs & BooleanConstant
     */
    int digest(Operator op) {
        if (this.op != op)
            throw new IllegalArgumentException();
        int d = 0;
        for (Iterator<BooleanValue> inputs = iterator(); inputs.hasNext();) {
            d += ((BooleanFormula) inputs.next()).hash(op);
        }
        return d;
    }

    /**
     * Returns the size of this accumulator.
     *
     * @return #this.inputs
     */
    public int size() {
        return inputs.size();
    }

    /**
     * Returns an iterator over this.components, in the increasing order of labels.
     * The returned iterator does not support removal.
     *
     * @return an iterator over this.components, in the increasing order of labels.
     */
    @Override
    public Iterator<BooleanValue> iterator() {
        return new Iterator<BooleanValue>() {

            final Iterator<IndexedEntry<BooleanValue>> iter = inputs.iterator();

            @Override
            public boolean hasNext() {
                return iter.hasNext();
            }

            @Override
            public BooleanValue next() {
                return iter.next().value();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
        // return inputs.iterator();
    }

    /**
     * Throws an unsupported operation exception.
     *
     * @throws UnsupportedOperationException
     */
    @Override
    BooleanValue negation() {
        throw new UnsupportedOperationException();
    }

    /**
     * Returns 0.
     *
     * @return 0.
     */
    @Override
    public int label() {
        return 0;
    }

    @Override
    public String toString() {
        return inputs.toString();
    }
}
