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
 * An temporal {@link kodkod.ast.Formula formula} with one child.
 * 
 * @specfield formula: Formula
 * @specfield op: TemporalOperator
 * @invariant op.unary()
 * @invariant children = 0->formula
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public final class UnaryTempFormula extends Formula {
    private final Formula formula;
    private final TemporalOperator temporalOperator;

    /**  
     * Constructs a new unary temporal formula: op formula
     * 
     * @ensures this.expression' = expression && this.op' = op
     * @throws NullPointerException  expression = null || op = null
     * @throws IllegalArgumentException  op.arity != 1 || op in {PRIME}
     */
    UnaryTempFormula(TemporalOperator op, Formula child) {
        if (!op.unary() || op == TemporalOperator.PRIME) {
            throw new IllegalArgumentException("Not a unary formula operator: " + op);
        }
        if (op == null || child == null) {
            throw new NullPointerException("null arg");
        }
        this.formula = child;
        this.temporalOperator = op;
    }

    /**
     * Returns this.formula.
     * @return this.formula
     */
    public Formula formula() { return formula; }

    /**
     * Returns this.op.
     * @return this.op
     */
    public TemporalOperator op() { return temporalOperator; }

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
    	return this.temporalOperator + "(" + formula + ")";
    }
}
