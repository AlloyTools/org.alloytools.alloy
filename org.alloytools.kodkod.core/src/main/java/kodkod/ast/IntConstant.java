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

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * An integer constant (literal).
 *
 * @specfield value: int
 * @invariant no children
 * @author Emina Torlak
 */
public final class IntConstant extends IntExpression {

    private final int value;

    /**
     * Constructs an int constant.
     *
     * @ensures this.value' = value
     */
    private IntConstant(int value) {
        this.value = value;
    }

    /**
     * Returns an IntConstant corresponding to the given value.
     *
     * @return {c: IntConstant | c.value = value}
     */
    public static IntConstant constant(int value) {
        return new IntConstant(value);
    }

    /**
     * Returns this.value.
     *
     * @return this.value
     */
    public int value() {
        return value;
    }

    /**
     * Return true if o is an IntConstant with the same value as this.
     *
     * @return o in IntConstant && o.value = this.value
     */
    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        else if (o instanceof IntConstant)
            return value == ((IntConstant) o).value;
        else
            return false;
    }

    /**
     * Return this.value
     *
     * @return this.value
     */
    @Override
    public int hashCode() {
        return value;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> I accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.IntExpression#accept(kodkod.ast.visitor.VoidVisitor)
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
        return String.valueOf(value);
    }

}
