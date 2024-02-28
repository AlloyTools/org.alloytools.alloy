/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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


import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * A temporal {@link kodkod.ast.Formula formula} with two children.
 * 
 * @specfield left: Formula
 * @specfield right: Formula
 * @specfield op: TemporalOperator
 * @invariant children = 0->left + 1->right
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public final class BinaryTempFormula extends Formula {
	private final TemporalOperator op;
    private final Formula left;
    private final Formula right;

    /**  
     * Constructs a new temporal binary formula:  left op right
     * 
     * @ensures this.left' = left && this.right' = right &&  this.op' = op
     * @throws NullPointerException  left = null || right = null || op = null
     * @throws IllegalArgumentException  op.arity != 2
     */
    BinaryTempFormula(Formula left, TemporalOperator op, Formula right) {
        if (!op.binary()) {
            throw new IllegalArgumentException("Not a unary operator: " + op);
        }
        if (op == null || left == null || right == null) {
            throw new NullPointerException("null arg");
        }
        this.left = left;
        this.right = right;
        this.op = op;
    }

    /**
     * Returns the left child of this.
     * @return this.left
     */
    public Formula left() { return left; }

    /**
     * Returns the right child of this.
     * @return this.right
     */
    public Formula right() { return right; }

    /**
     * Returns the operator of this.
     * @return this.op
     */
    public TemporalOperator op() { return op; }

    /**
     * {@inheritDoc}
     * @see kodkod.ast.Formula#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    public <E, F, D, I> F accept(ReturnVisitor<E, F, D, I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     * @see kodkod.ast.Node#toString()
     */
    public String toString() {
        return  "(" + this.left+" " + this.op + " "+ this.right + ")";
    }
}
