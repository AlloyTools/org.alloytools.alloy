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

import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * A variable declaration, such as 'x : lone X'. Declarations are used with
 * quantified formulas and comprehension expressions.
 *
 * @specfield variable: Variable
 * @specfield expression: Expression
 * @specfield multiplicity: LONE + ONE + SOME + SET
 * @invariant variable.arity = expression.arity
 * @invariant children = 0->variable + 1->expression
 * @author Emina Torlak
 */
public final class Decl extends Decls {

    private final Variable     variable;
    private final Multiplicity mult;
    private final Expression   expression;

    /**
     * Constructs a new declaration from the specified variable and expression, with
     * the specified order.
     *
     * @ensures this.variable' = variable && this.expression' = expression &&
     *          this.multiplicity' = mult
     * @throws NullPointerException variable = null || expression = null || mult =
     *             null
     * @throws IllegalArgumentException variable.arity != expression.arity
     */
    Decl(Variable variable, Multiplicity mult, Expression expression) {
        if (mult == Multiplicity.NO)
            throw new IllegalArgumentException("NO is not a valid multiplicity in a declaration.");
        if (variable.arity() != expression.arity())
            throw new IllegalArgumentException("Unmatched arities in a declaration: " + variable + " and " + expression);
        if (mult != Multiplicity.SET && expression.arity() > 1)
            throw new IllegalArgumentException("Cannot use multiplicity " + mult + " with an expression of arity > 1.");
        this.variable = variable;
        this.mult = mult;
        this.expression = expression;
    }

    /**
     * Returns the variable in this declaration.
     *
     * @return this.variable
     */
    public Variable variable() {
        return variable;
    }

    /**
     * Returns the multiplicity in this declaration.
     *
     * @return this.multiplicity
     */
    public Multiplicity multiplicity() {
        return mult;
    }

    /**
     * Returns the expression in this declaration.
     *
     * @return this.exresssion
     */
    public Expression expression() {
        return expression;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> D accept(ReturnVisitor<E,F,D,I> visitor) {
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
        return variable + ": " + mult + " " + expression;
    }

}
