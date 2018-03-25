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
package kodkod.ast;

import java.util.Iterator;

import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;

/**
 * A {@linkplain kodkod.ast.Formula formula} with more than two children,
 * composed with an nary {@linkplain FormulaOperator operator}.
 *
 * @specfield op: FormulaOperator
 * @invariant op.nary()
 * @invariant #children > 2
 * @author Emina Torlak
 */
public final class NaryFormula extends Formula implements Iterable<Formula> {

    private final FormulaOperator op;
    private final Formula[]       children;

    /**
     * Constructs a new composite Formula: op(children)
     *
     * @requires children array is not modified while in use by this composite
     *           Formula
     * @requires some op.op[children]
     * @ensures this.children' = children && this.op' = op
     */
    NaryFormula(FormulaOperator op, Formula[] children) {
        assert children.length > 2;
        if (!op.nary())
            throw new IllegalArgumentException("Cannot construct an nary formula using the non-nary operator " + op);
        this.op = op;
        this.children = children;
    }

    /**
     * Returns the operator of this.
     *
     * @return this.op
     */
    public FormulaOperator op() {
        return op;
    }

    /**
     * Returns the number of children of this formula.
     *
     * @return #this.children
     */
    public int size() {
        return children.length;
    }

    /**
     * Returns the ith child of this formula.
     *
     * @requires 0 <= i < #this.children
     * @return this.children[i]
     */
    public Formula child(int i) {
        return children[i];
    }

    /**
     * Returns an iterator over this formula's children, in the increasing order of
     * indices.
     *
     * @return an iterator over this formula's children, in the increasing order of
     *         indices.
     */
    @Override
    public Iterator<Formula> iterator() {
        return Containers.iterate(children);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Formula#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> F accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    @Override
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#toString()
     */
    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder("(");
        s.append(child(0));
        for (int i = 1, size = size(); i < size; i++) {
            s.append(" ");
            s.append(op);
            s.append(" ");
            s.append(child(i));
        }
        s.append(")");
        return s.toString();
    }

}
