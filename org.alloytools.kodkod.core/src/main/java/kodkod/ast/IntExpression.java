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

import static kodkod.ast.operator.IntCastOperator.BITSETCAST;
import static kodkod.ast.operator.IntCastOperator.INTCAST;
import static kodkod.ast.operator.IntCompOperator.EQ;
import static kodkod.ast.operator.IntCompOperator.GT;
import static kodkod.ast.operator.IntCompOperator.GTE;
import static kodkod.ast.operator.IntCompOperator.LT;
import static kodkod.ast.operator.IntCompOperator.LTE;
import static kodkod.ast.operator.IntCompOperator.NEQ;
import static kodkod.ast.operator.IntOperator.ABS;
import static kodkod.ast.operator.IntOperator.AND;
import static kodkod.ast.operator.IntOperator.DIVIDE;
import static kodkod.ast.operator.IntOperator.MINUS;
import static kodkod.ast.operator.IntOperator.MODULO;
import static kodkod.ast.operator.IntOperator.MULTIPLY;
import static kodkod.ast.operator.IntOperator.NEG;
import static kodkod.ast.operator.IntOperator.NOT;
import static kodkod.ast.operator.IntOperator.OR;
import static kodkod.ast.operator.IntOperator.PLUS;
import static kodkod.ast.operator.IntOperator.SGN;
import static kodkod.ast.operator.IntOperator.SHA;
import static kodkod.ast.operator.IntOperator.SHL;
import static kodkod.ast.operator.IntOperator.SHR;
import static kodkod.ast.operator.IntOperator.XOR;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;

import kodkod.ast.operator.IntCastOperator;
import kodkod.ast.operator.IntCompOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.util.collections.Containers;

/**
 * A Node whose value is an integer rather than a relational expression.
 *
 * @author Emina Torlak
 */
public abstract class IntExpression extends Node {

    /**
     * Constructs an IntExpression.
     */
    IntExpression() {}

    /**
     * Returns a formula stating that the given int expression and this have the
     * same value. The effect of this method is the same as calling this.compare(EQ,
     * intExpr).
     *
     * @return this.compare(EQ, intExpr)
     */
    public final Formula eq(IntExpression intExpr) {
        return this.compare(EQ, intExpr);
    }

    public final Formula neq(IntExpression intExpr) {
        return this.compare(NEQ, intExpr);
    }

    /**
     * Returns a formula stating that the value of this int expression is less than
     * the value of the given int expression The effect of this method is the same
     * as calling this.compare(LT, intExpr).
     *
     * @return this.compare(LT, intExpr)
     */
    public final Formula lt(IntExpression intExpr) {
        return this.compare(LT, intExpr);
    }

    /**
     * Returns a formula stating that the value of this int expression is less than
     * or equal to the value of the given int expression The effect of this method
     * is the same as calling this.compare(LTE, intExpr).
     *
     * @return this.compare(LTE, intExpr)
     */
    public final Formula lte(IntExpression intExpr) {
        return this.compare(LTE, intExpr);
    }

    /**
     * Returns a formula stating that the value of this int expression is greater
     * than the value of the given int expression The effect of this method is the
     * same as calling this.compare(GT, intExpr).
     *
     * @return this.compare(GT, intExpr)
     */
    public final Formula gt(IntExpression intExpr) {
        return this.compare(GT, intExpr);
    }

    /**
     * Returns a formula stating that the value of this int expression is greater
     * than or equal to the value of the given int expression The effect of this
     * method is the same as calling this.compare(GTE, intExpr).
     *
     * @return this.compare(GTE, intExpr)
     */
    public final Formula gte(IntExpression intExpr) {
        return this.compare(GTE, intExpr);
    }

    /**
     * Returns a formula comparing this and the given integer expression using the
     * specified operator.
     *
     * @return {f: Formula | f.left = this and f.right = intExpr and f.op = op }
     */
    public Formula compare(IntCompOperator op, IntExpression intExpr) {
        if (op == null || intExpr == null)
            throw new NullPointerException();
        return new IntComparisonFormula(this, op, intExpr);
    }

    /**
     * Returns an integer expression that is the sum of all values that this integer
     * expression can take given the provided declarations.
     *
     * @return {e: IntExpression | e.decls = decls and e.intExpr = this }
     */
    public final IntExpression sum(Decls decls) {
        return new SumExpression(decls, this);
    }

    /**
     * Returns an IntExpression that represents the sum of this and the given int
     * node. The effect of this method is the same as calling this.compose(PLUS,
     * intExpr).
     *
     * @return this.compose(PLUS, intExpr)
     */
    public final IntExpression plus(IntExpression intExpr) {
        return compose(PLUS, intExpr);
    }

    /**
     * Returns an IntExpression that represents the difference between this and the
     * given int node. The effect of this method is the same as calling
     * this.compose(MINUS, intExpr).
     *
     * @return this.compose(MINUS, intExpr)
     */
    public final IntExpression minus(IntExpression intExpr) {
        return compose(MINUS, intExpr);
    }

    /**
     * Returns an IntExpression that represents the product of this and the given
     * int node. The effect of this method is the same as calling
     * this.compose(MULTIPLY, intExpr).
     *
     * @return this.compose(MULTIPLY, intExpr)
     */
    public final IntExpression multiply(IntExpression intExpr) {
        return compose(MULTIPLY, intExpr);
    }

    /**
     * Returns an IntExpression that represents the quotient of the division between
     * this and the given int node. The effect of this method is the same as calling
     * this.compose(DIVIDE, intExpr).
     *
     * @return this.compose(DIVIDE, intExpr)
     */
    public final IntExpression divide(IntExpression intExpr) {
        return compose(DIVIDE, intExpr);
    }

    /**
     * Returns an IntExpression that represents the remainder of the division
     * between this and the given int node. The effect of this method is the same as
     * calling this.compose(MODULO, intExpr).
     *
     * @return this.compose(MODULO, intExpr)
     */
    public final IntExpression modulo(IntExpression intExpr) {
        return compose(MODULO, intExpr);
    }

    /**
     * Returns an IntExpression that represents the bitwise AND of this and the
     * given int node. The effect of this method is the same as calling
     * this.compose(AND, intExpr).
     *
     * @return this.compose(AND, intExpr)
     */
    public final IntExpression and(IntExpression intExpr) {
        return compose(AND, intExpr);
    }

    /**
     * Returns an IntExpression that represents the bitwise OR of this and the given
     * int node. The effect of this method is the same as calling this.compose(OR,
     * intExpr).
     *
     * @return this.compose(OR, intExpr)
     */
    public final IntExpression or(IntExpression intExpr) {
        return compose(OR, intExpr);
    }

    /**
     * Returns an IntExpression that represents the bitwise XOR of this and the
     * given int node. The effect of this method is the same as calling
     * this.compose(XOR, intExpr).
     *
     * @return this.compose(XOR, intExpr)
     */
    public final IntExpression xor(IntExpression intExpr) {
        return compose(XOR, intExpr);
    }

    /**
     * Returns an IntExpression that represents the left shift of this by the given
     * int node. The effect of this method is the same as calling this.compose(SHL,
     * intExpr).
     *
     * @return this.compose(SHL, intExpr)
     */
    public final IntExpression shl(IntExpression intExpr) {
        return compose(SHL, intExpr);
    }

    /**
     * Returns an IntExpression that represents the right shift of this and the
     * given int node, with zero extension. The effect of this method is the same as
     * calling this.compose(SHR, intExpr).
     *
     * @return this.compose(SHR, intExpr)
     */
    public final IntExpression shr(IntExpression intExpr) {
        return compose(SHR, intExpr);
    }

    /**
     * Returns an IntExpression that represents the right shift of this and the
     * given int node, with sign extension. The effect of this method is the same as
     * calling this.compose(SHA, intExpr).
     *
     * @return this.compose(SHA, intExpr)
     */
    public final IntExpression sha(IntExpression intExpr) {
        return compose(SHA, intExpr);
    }

    /**
     * Returns an expression that combines this and the given integer expression
     * using the specified operator.
     *
     * @requires op.binary()
     * @return {e: IntExpression | e.left = this and e.right = intExpr and e.op = op
     *         }
     */
    public final IntExpression compose(IntOperator op, IntExpression intExpr) {
        if (op == null || intExpr == null)
            throw new NullPointerException();
        return new BinaryIntExpression(this, op, intExpr);
    }

    /**
     * Returns the sum of the given int expressions. The effect of this method is
     * the same as calling compose(PLUS, intExprs).
     *
     * @return compose(PLUS, intExprs)
     */
    public static IntExpression plus(IntExpression... intExprs) {
        return compose(PLUS, intExprs);
    }

    /**
     * Returns the plus of the given int expressions. The effect of this method is
     * the same as calling compose(PLUS, intExprs).
     *
     * @return compose(PLUS, intExprs)
     */
    public static IntExpression plus(Collection< ? extends IntExpression> intExprs) {
        return compose(PLUS, intExprs);
    }

    /**
     * Returns the product of the given int expressions. The effect of this method
     * is the same as calling compose(MULTIPLY, intExprs).
     *
     * @return compose(MULTIPLY, intExprs)
     */
    public static IntExpression multiply(IntExpression... intExprs) {
        return compose(MULTIPLY, intExprs);
    }

    /**
     * Returns the product of the given int expressions. The effect of this method
     * is the same as calling compose(MULTIPLY, intExprs).
     *
     * @return compose(MULTIPLY, intExprs)
     */
    public static IntExpression multiply(Collection< ? extends IntExpression> intExprs) {
        return compose(MULTIPLY, intExprs);
    }

    /**
     * Returns the bitwise and of the given int expressions. The effect of this
     * method is the same as calling compose(AND, intExprs).
     *
     * @return compose(AND, intExprs)
     */
    public static IntExpression and(IntExpression... intExprs) {
        return compose(AND, intExprs);
    }

    /**
     * Returns the bitwise and of the given int expressions. The effect of this
     * method is the same as calling compose(AND, intExprs).
     *
     * @return compose(AND, intExprs)
     */
    public static IntExpression and(Collection< ? extends IntExpression> intExprs) {
        return compose(AND, intExprs);
    }

    /**
     * Returns the bitwise or of the given int expressions. The effect of this
     * method is the same as calling compose(OR, intExprs).
     *
     * @return compose(OR, intExprs)
     */
    public static IntExpression or(IntExpression... intExprs) {
        return compose(OR, intExprs);
    }

    /**
     * Returns the bitwise or of the given int expressions. The effect of this
     * method is the same as calling compose(OR, intExprs).
     *
     * @return compose(OR, intExprs)
     */
    public static IntExpression or(Collection< ? extends IntExpression> intExprs) {
        return compose(OR, intExprs);
    }

    /**
     * Returns the composition of the given int expressions using the given
     * operator.
     *
     * @requires intExprs.length = 2 => op.binary(), intExprs.length > 2 =>
     *           op.nary()
     * @return intExprs.length=1 => intExprs[0] else {e: IntExpression | e.children
     *         = intExprs and e.op = this }
     */
    public static IntExpression compose(IntOperator op, IntExpression... intExprs) {
        switch (intExprs.length) {
            case 0 :
                throw new IllegalArgumentException("Expected at least one argument: " + Arrays.toString(intExprs));
            case 1 :
                return intExprs[0];
            case 2 :
                return new BinaryIntExpression(intExprs[0], op, intExprs[1]);
            default :
                return new NaryIntExpression(op, Containers.copy(intExprs, new IntExpression[intExprs.length]));
        }
    }

    /**
     * Returns the composition of the given int expressions using the given
     * operator.
     *
     * @requires intExprs.length = 2 => op.binary(), intExprs.length > 2 =>
     *           op.nary()
     * @return intExprs.size() = 1 => intExprs.iterator().next() else {e:
     *         IntExpression | e.children = intExprs.toArray() and e.op = this }
     */
    public static IntExpression compose(IntOperator op, Collection< ? extends IntExpression> intExprs) {
        switch (intExprs.size()) {
            case 0 :
                throw new IllegalArgumentException("Expected at least one argument: " + intExprs);
            case 1 :
                return intExprs.iterator().next();
            case 2 :
                final Iterator< ? extends IntExpression> itr = intExprs.iterator();
                return new BinaryIntExpression(itr.next(), op, itr.next());
            default :
                return new NaryIntExpression(op, intExprs.toArray(new IntExpression[intExprs.size()]));
        }
    }

    /**
     * Returns an IntExpression that represents the negation of this int expression.
     * The effect of this method is the same as calling this.apply(NEG).
     *
     * @return this.apply(NEG)
     */
    public final IntExpression negate() {
        return apply(NEG);
    }

    /**
     * Returns an IntExpression that represents the bitwise negation of this int
     * expression. The effect of this method is the same as calling this.apply(NOT).
     *
     * @return this.apply(NOT)
     */
    public final IntExpression not() {
        return apply(NOT);
    }

    /**
     * Returns an IntExpression that represents the absolute value of this int
     * expression. The effect of this method is the same as calling this.apply(ABS).
     *
     * @return this.apply(ABS)
     */
    public final IntExpression abs() {
        return apply(ABS);
    }

    /**
     * Returns an IntExpression that represents the sign of this int expression. The
     * effect of this method is the same as calling this.apply(SGN).
     *
     * @return this.apply(SGN)
     */
    public final IntExpression signum() {
        return apply(SGN);
    }

    /**
     * Returns an expression that represents the application of the given unary
     * operator to this integer expression.
     *
     * @requires op.unary()
     * @return {e: IntExpression | e.op = op and e.intExpr = this }
     */
    public final IntExpression apply(IntOperator op) {
        return new UnaryIntExpression(op, this);
    }

    /**
     * Returns an expression whose meaning is the singleton set containing the atom
     * that represents the integer given by this integer expression. The effect of
     * this method is the same as calling this.cast(INTCAST).
     *
     * @return this.cast(INTCAST)
     */
    public final Expression toExpression() {
        return cast(INTCAST);
    }

    /**
     * Returns an expression whose meaning is the set containing the atoms that
     * represent the powers of 2 (bits) present in this integer expression. The
     * effect of this method is the same as calling this.cast(BITSETCAST).
     *
     * @return this.cast(BITSETCAST)
     */
    public final Expression toBitset() {
        return cast(BITSETCAST);
    }

    /**
     * Returns an expression that is the relational representation of this integer
     * expression specified by the given operator.
     *
     * @return an expression that is the relational representation of this integer
     *         expression specified by the given operator.
     */
    public final Expression cast(IntCastOperator op) {
        if (op == null)
            throw new NullPointerException();
        return new IntToExprCast(this, op);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public abstract <E, F, D, I> I accept(ReturnVisitor<E,F,D,I> visitor);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    @Override
    public abstract void accept(VoidVisitor visitor);

}
