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

import kodkod.util.ints.Ints;

/**
 * A logic gate with two or more inputs; an AND or an OR gate.
 *
 * @specfield op: Operator.Binary
 * @invariant #inputs > 1
 * @invariant some components.this => label in [1..Integer.MAX_VALUE), label in
 *            [0..Integer.MAX_VALUE)
 * @invariant no c1, c2: inputs | c1.label = -c2.label
 * @invariant this.label > 0 => all c: inputs | |c.label| < this.label
 * @author Emina Torlak
 */
public abstract class MultiGate extends BooleanFormula {

    final Operator.Nary op;

    private final int   label, labelhash, hashcode;

    /**
     * Constructs a new MultiGate gate with the given operator and label.
     *
     * @requires op != null && label >= 0
     * @ensures this.op' = op && this.label' = label
     */
    MultiGate(Operator.Nary op, int label, int hashcode) {
        super(null);
        assert op != null;
        assert label >= 0;
        this.op = op;
        this.label = label;
        this.labelhash = Ints.superFastHash(label);
        this.hashcode = hashcode;
    }

    /**
     * Returns the label for this value.
     *
     * @return this.label
     */
    @Override
    public final int label() {
        return label;
    }

    /**
     * Returns the operator used to combine the input variables of this connective
     * gate.
     *
     * @return this.op
     */
    @Override
    public final Operator.Nary op() {
        return op;
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
     * Returns a string representation of this multigate.
     *
     * @return a string representation of this multigate.
     */
    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder("(");
        final Iterator<BooleanFormula> children = iterator();
        builder.append(children.next());
        while (children.hasNext()) {
            builder.append(op);
            builder.append(children.next());
        }
        builder.append(")");
        return builder.toString();
    }

    /**
     * Returns a hashcode for this gate. The hashcode obeys the Object contract.
     *
     * @return a hashcode for this gate.
     */
    @Override
    public final int hashCode() {
        return hashcode;
    }

    /**
     * Returns the digest of this formula that would be used to compute the digest
     * of the composition of this and some other formula using the given operator.
     * Specifically, if op = this.op, then the sum of this circuit's irreducible
     * inputs' hashes (with respect to op) is returned. Otherwise, the superFastHash
     * of this.label is returned.
     *
     * @return this.op = op => this.op.hash(this.inputs),
     *         Ints.superFastHash(this.label)
     */
    @Override
    final int hash(Operator op) {
        return op == this.op ? hashcode : labelhash;
    }
}
