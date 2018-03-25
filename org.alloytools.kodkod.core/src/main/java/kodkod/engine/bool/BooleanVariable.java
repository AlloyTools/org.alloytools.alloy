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

import kodkod.util.collections.Containers;
import kodkod.util.ints.Ints;

/**
 * Represents a boolean variable.
 *
 * @invariant op = Operator.VAR
 * @invariant no inputs && label in [1, ..., Integer.MAX_VALUE)
 * @author Emina Torlak
 */
public final class BooleanVariable extends BooleanFormula {

    final int         label;
    private final int hashcode;

    /**
     * Constructs a new BooleanVariable with the given label.
     *
     * @requires label != 0
     * @ensures this.label' = label
     */
    BooleanVariable(int label) {
        super(null);
        assert label != 0;
        this.label = label;
        this.hashcode = Ints.superFastHash(label);
    }

    /**
     * Returns a hash of this variable's label.
     *
     * @return Ints.superFastHash(this.label)
     */
    @Override
    int hash(Operator op) {
        return hashcode;
    }

    /**
     * Returns the label for this value.
     *
     * @return this.label
     */
    @Override
    public int label() {
        return label;
    }

    /**
     * Returns a string representation of this variable.
     *
     * @return a string representation of this variable.
     */
    @Override
    public String toString() {
        return Integer.toString(label);
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
     * Returns the VAR operator.
     *
     * @return Operator.VAR
     */
    @Override
    public Operator op() {
        return Operator.VAR;
    }

    /**
     * Returns an empty iterator.
     *
     * @return an empty iterator
     */
    @Override
    public Iterator<BooleanFormula> iterator() {
        return Containers.emptyIterator();
    }

    /**
     * Returns 0.
     *
     * @return 0
     */
    @Override
    public int size() {
        return 0;
    }

    /**
     * Throws an IndexOutOfBoundsException.
     *
     * @throws IndexOutOfBoundsException
     */
    @Override
    public BooleanFormula input(int i) {
        throw new IndexOutOfBoundsException();
    }

    /**
     * Returns a hashcode for this variable.
     *
     * @return a hashcode for this variable.
     */
    @Override
    public int hashCode() {
        return hashcode;
    }
}
