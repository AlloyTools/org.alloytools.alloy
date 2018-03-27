/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.ast.ExprUnary.Op.NOOP;
import static edu.mit.csail.sdg.ast.Type.EMPTY;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

/**
 * Immutable; represents a formula or expression.
 * <p>
 * <b>Invariant:</b> pos!=null <br>
 * <b>Invariant:</b> type!=null <br>
 * <b>Invariant:</b> type==EMPTY iff errors.size()>0 <br>
 * <b>Invariant:</b> mult==0 || mult==1 || mult==2 <br>
 * <b>Invariant:</b> weight>0
 */

public abstract class Expr extends Browsable {

    /**
     * The filename, line, and column position in the original Alloy model file
     * (cannot be null).
     */
    public final Pos pos;

    /**
     * The filename, line, and column position in the original Alloy model file of
     * the closing bracket).
     */
    public final Pos closingBracket;

    /**
     * The type for this node; EMPTY if it is not well-typed.
     */
    final Type       type;

    /**
     * Return the type for this node; EMPTY if it is not well-typed.
     */
    public final Type type() {
        return type;
    }

    /**
     * The list of errors on this node; nonempty iff this.type==EMPTY
     */
    public final JoinableList<Err> errors;

    /**
     * This field records whether the node is a multiplicity constraint. <br>
     * If it's 2, that means it is an arrow multiplicity constraint (X ?->? X), or
     * has the form (A -> B) where A and/or B is an arrow multiplicity constraint.
     * <br>
     * If it's 1, that means it is a multiplicity constraint of the form (? X) <br>
     * If it's 0, that means it does not have either form.
     */
    public final int               mult;

    /**
     * Each leaf Expr has a weight value (which can be 0 or higher); by default,
     * each nonleaf Expr's weight is the sum of its children's weights.
     */
    public final long              weight;

    /** True if this expression is not fully resolved. */
    public final boolean           ambiguous;

    private Clause                 referenced;

    /** This is an unmodifiable empty list of Err objects. */
    static final JoinableList<Err> emptyListOfErrors = new JoinableList<Err>();

    // ================================================================================================================//

    /**
     * Constructs a new expression node
     *
     * @param pos - the original position in the file (can be null if unknown)
     * @param closingBracket - the original position of the closing bracket (can be
     *            null if unknown)
     * @param ambiguous - true if this node is ExprChoice or it contains an
     *            ExprChoice subnode
     * @param type - the type
     * @param mult - the multiplicity (which must be 0, 1, or 2) <br>
     *            If it's 2, that means it is a multiplicity constraint (X ?->? X),
     *            or has the form (A -> B) where A and/or B is a multiplicity
     *            constraint. <br>
     *            If it's 1, that means it is a multiplicity constraint of the form
     *            (? X) <br>
     *            If it's 0, that means it does not have either form.
     * @param weight - the weight of this node and all subnodes
     * @param errors - the list of errors associated with this Expr node (can be
     *            null if there are none)
     */
    Expr(Pos pos, Pos closingBracket, boolean ambiguous, Type type, int mult, long weight, JoinableList<Err> errors) {
        this.pos = (pos == null ? Pos.UNKNOWN : pos);
        this.closingBracket = (closingBracket == null ? Pos.UNKNOWN : closingBracket);
        this.ambiguous = ambiguous;
        if (errors == null)
            errors = emptyListOfErrors;
        if (type == EMPTY && errors.size() == 0)
            errors = errors.make(new ErrorType(pos, "This expression failed to be typechecked " + pos));
        this.mult = (mult < 0 || mult > 2) ? 0 : mult;
        this.type = (errors.size() > 0 || type == null) ? EMPTY : type;
        this.weight = (weight > 0) ? weight : 0;
        this.errors = errors;
    }

    /** This must only be called by Sig's constructor. */
    Expr(Pos pos, Type type) {
        this.closingBracket = Pos.UNKNOWN;
        this.ambiguous = false;
        this.errors = emptyListOfErrors;
        this.pos = (pos == null ? Pos.UNKNOWN : pos);
        this.type = (type == null || type == EMPTY) ? Type.make((PrimSig) this) : type;
        this.mult = 0;
        this.weight = 0;
    }

    /** {@inheritDoc} */
    @Override
    public final Pos pos() {
        return pos;
    }

    /**
     * Print a textual description of it and all subnodes to a StringBuilder, with
     * the given level of indentation. (If indent<0, it will be printed in one line
     * without line break)
     */
    public abstract void toString(StringBuilder out, int indent);

    /**
     * Print a brief text description of it and all subnodes.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(sb, -1);
        return sb.toString();
    }

    /** {@inheritDoc} */
    @Override
    public final int hashCode() {
        return super.hashCode();
    }

    /** {@inheritDoc} */
    @Override
    public final boolean equals(Object other) {
        return super.equals(other);
    }

    // ================================================================================================================//

    /** Accepts the return visitor. */
    public abstract <T> T accept(VisitReturn<T> visitor) throws Err;

    /**
     * Converts this into a "formula" if possible; otherwise, returns an Expr with a
     * nonempty error list
     */
    public final Expr typecheck_as_formula() {
        if (!errors.isEmpty() || type.is_bool)
            return this;
        String msg = "This must be a formula expression.\nInstead, it has the following possible type(s):\n" + type;
        return NOOP.make(null, this, new ErrorType(span(), msg), 0);
    }

    /**
     * Converts this into an "integer expression" if possible; otherwise, returns an
     * Expr with a nonempty error list
     */
    public final Expr typecheck_as_int() {
        if (!errors.isEmpty())
            return this;
        if (type.is_small_int())
            return this;
        if (type.is_int()) {
            return cast2int();
        }
        // else: error
        String msg = "This must be an integer expression.\nInstead, it has the following possible type(s):\n" + type;
        return NOOP.make(null, this, new ErrorType(span(), msg), 0);
    }

    /**
     * Converts this into a "set or relation" if possible; otherwise, returns an
     * Expr with a nonempty error list
     */
    public final Expr typecheck_as_set() {
        if (!errors.isEmpty())
            return this;
        if (type.is_small_int())
            return cast2sigint();
        if (type.is_int())
            return this;
        if (type.size() > 0)
            return this;
        // else: error
        String msg = "This must be a set or relation.\nInstead, it has the following possible type(s):\n" + type;
        return NOOP.make(null, this, new ErrorType(span(), msg), 0);
    }

    // ================================================================================================================//

    /**
     * Resolves this expression if ambiguous. (And if t.size()>0, it represents the
     * set of tuples whose presence/absence is relevent to the parent expression)
     * (Note: it's possible for t to be EMPTY, or even ambiguous!)
     * <p>
     * On success: the return value will be well-typed and unambiguous
     * <p>
     * On failure: the return value's "errors" list will be nonempty
     * <p>
     * If we detect any type warnings, we will add the type warnings to the
     * "warnings" collection.
     *
     * @param warnings - the list that will receive any warning we generate; can be
     *            null if we wish to ignore warnings
     */
    public abstract Expr resolve(Type t, Collection<ErrorWarning> warnings);

    /**
     * Converts this into a "formula" if possible, then resolves it if ambiguous.
     * <p>
     * On success: the return value will be a well-typed unambiguous formula
     * expression
     * <p>
     * On failure: the return value's "errors" list will be nonempty
     * <p>
     * If we detect any type warnings, we will add the type warnings to the
     * "warnings" collection.
     *
     * @param warnings - the list that will receive any warning we generate; can be
     *            null if we wish to ignore warnings
     */
    public final Expr resolve_as_formula(Collection<ErrorWarning> warnings) {
        return typecheck_as_formula().resolve(Type.FORMULA, warnings).typecheck_as_formula();
    }

    /**
     * Converts this into an "integer expression" if possible, then resolves it if
     * ambiguous.
     * <p>
     * On success: the return value will be a well-typed unambiguous integer
     * expression
     * <p>
     * On failure: the return value's "errors" list will be nonempty
     * <p>
     * If we detect any type warnings, we will add the type warnings to the
     * "warnings" collection.
     *
     * @param warnings - the list that will receive any warning we generate; can be
     *            null if we wish to ignore warnings
     */
    public final Expr resolve_as_int(Collection<ErrorWarning> warnings) {
        return typecheck_as_int().resolve(Type.smallIntType(), warnings).typecheck_as_int();
    }

    /**
     * Converts this into a "set or relation" if possible, then resolves it if
     * ambiguous.
     * <p>
     * On success: the return value will be a well-typed unambiguous set or relation
     * expression
     * <p>
     * On failure: the return value's "errors" list will be nonempty
     * <p>
     * If we detect any type warnings, we will add the type warnings to the
     * "warnings" collection.
     *
     * @param warnings - the list that will receive any warning we generate; can be
     *            null if we wish to ignore warnings
     */
    public final Expr resolve_as_set(Collection<ErrorWarning> warnings) {
        Expr x = typecheck_as_set();
        Type t = x.type;
        return x.resolve(Type.removesBoolAndInt(t), warnings).typecheck_as_set();
    }

    // ================================================================================================================//

    /**
     * Returns true if we can determine the two expressions are equivalent; may
     * sometimes return false.
     */
    public boolean isSame(Expr obj) {
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        return obj == this;
    }

    /** Remove the "NOP" in front of an expression (if any). */
    public final Expr deNOP() {
        Expr x = this;
        while (x instanceof ExprUnary && ((ExprUnary) x).op == ExprUnary.Op.NOOP)
            x = ((ExprUnary) x).sub;
        return x;
    }

    /**
     * If this is loneOf/oneOf/someOf/exactlyOf expression, return
     * loneOf/oneOf/someOf/exactlyOf, otherwise returns setOf.
     */
    public final ExprUnary.Op mult() {
        Expr x = this;
        while (x instanceof ExprUnary) {
            ExprUnary.Op op = ((ExprUnary) x).op;
            if (op == ExprUnary.Op.NOOP) {
                x = ((ExprUnary) x).sub;
                continue;
            }
            if (op == ExprUnary.Op.ONEOF || op == ExprUnary.Op.LONEOF || op == ExprUnary.Op.SOMEOF || op == ExprUnary.Op.EXACTLYOF)
                return op;
            break;
        }
        return ExprUnary.Op.SETOF;
    }

    /**
     * A return visitor that determines whether the node (or a subnode) contains a
     * predicate/function call.
     */
    private static final VisitQuery<Object> hasCall = new VisitQuery<Object>() {

        @Override
        public final Object visit(ExprCall x) {
            return this;
        }
    };

    /**
     * Returns true if the node is well-typed, unambiguous, and contains a
     * predicate/function call.
     */
    final boolean hasCall() {
        boolean ans = !ambiguous && errors.isEmpty();
        if (ans) {
            try {
                ans = accept(hasCall) != null;
            } catch (Err ex) {
                ans = false;
            }
        } // This exception should not occur
        return ans;
    }

    /**
     * Returns true if the node is well-typed, unambiguous, and contains the given
     * variable.
     */
    public final boolean hasVar(final ExprVar goal) {
        if (ambiguous || !errors.isEmpty())
            return false;
        VisitQuery<Object> hasVar = new VisitQuery<Object>() {

            @Override
            public final Object visit(ExprVar x) throws Err {
                if (x == goal)
                    return this;
                else
                    return null;
            }
        };
        boolean ans;
        try {
            ans = accept(hasVar) != null;
        } catch (Err ex) {
            return false;
        } // This exception should not occur
        return ans;
    }

    /**
     * Transitively returns a set that contains all predicates/functions that this
     * expression calls directly or indirectly.
     */
    public final Iterable<Func> findAllFunctions() {
        final LinkedHashSet<Func> seen = new LinkedHashSet<Func>();
        final List<Func> todo = new ArrayList<Func>();
        final VisitQuery<Object> q = new VisitQuery<Object>() {

            @Override
            public final Object visit(ExprCall x) {
                if (seen.add(x.fun))
                    todo.add(x.fun);
                return null;
            }
        };
        try {
            q.visitThis(this);
            while (!todo.isEmpty()) {
                q.visitThis(todo.remove(todo.size() - 1).getBody());
            }
        } catch (Err ex) {} // Exception should not occur
        return seen;
    }

    /**
     * Returns the height of the abstract syntax tree starting from this node.
     */
    public abstract int getDepth();

    // ================================================================================//
    // Below are convenience methods for building up expressions from
    // subexpressions. //
    // ================================================================================//

    /**
     * Returns the formula (this and x)
     * <p>
     * this and x must both be formulas
     * <p>
     * Note: as a special guarantee, if x==null, then the method will return this
     * Expr object as-is.
     */
    public final Expr and(Expr x) {
        return (x == null) ? this : ExprBinary.Op.AND.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this or x)
     * <p>
     * this and x must both be formulas
     * <p>
     * Note: as a special guarantee, if x==null, then the method will return this
     * Expr object as-is.
     */
    public final Expr or(Expr x) {
        return (x == null) ? this : ExprBinary.Op.OR.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this iff x)
     * <p>
     * this and x must both be formulas
     */
    public final Expr iff(Expr x) {
        return ExprBinary.Op.IFF.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this implies x)
     * <p>
     * this and x must both be formulas
     */
    public final Expr implies(Expr x) {
        return ExprBinary.Op.IMPLIES.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this.x)
     * <p>
     * 1. this must be a set or relation
     * <p>
     * 2. x must be a set or relation
     * <p>
     * 3. at most one of them can be a unary set
     */
    public final Expr join(Expr x) {
        return ExprBinary.Op.JOIN.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this <: x)
     * <p>
     * this must be a unary set
     * <p>
     * x must be a set or relation
     */
    public final Expr domain(Expr x) {
        return ExprBinary.Op.DOMAIN.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this :> x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a unary set
     */
    public final Expr range(Expr x) {
        return ExprBinary.Op.RANGE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this intersects x)
     * <p>
     * this and x must be expressions with the same arity
     */
    public final Expr intersect(Expr x) {
        return ExprBinary.Op.INTERSECT.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this++x)
     * <p>
     * this and x must be expressions with the same arity
     */
    public final Expr override(Expr x) {
        return ExprBinary.Op.PLUSPLUS.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this+x)
     * <p>
     * this and x must be expressions with the same arity, or both be integer
     * expressions
     * <p>
     * Note: as a special guarantee, if x==null, then the method will return this
     * Expr object as-is.
     */
    public final Expr plus(Expr x) {
        return (x == null) ? this : ExprBinary.Op.PLUS.make(span().merge(x.span()), null, this, x);
    }

    public final Expr iplus(Expr x) {
        return (x == null) ? this : ExprBinary.Op.IPLUS.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this-x)
     * <p>
     * this and x must be expressions with the same arity, or both be integer
     * expressions
     */
    public final Expr minus(Expr x) {
        return ExprBinary.Op.MINUS.make(span().merge(x.span()), null, this, x);
    }

    public final Expr iminus(Expr x) {
        return ExprBinary.Op.IMINUS.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula "this.mul[x]" (the result of multiplying this by x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr mul(Expr x) {
        return ExprBinary.Op.MUL.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula "this.div[x]" (the quotient of dividing this by x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr div(Expr x) {
        return ExprBinary.Op.DIV.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula "this.rem[x]" (the remainder of dividing this by x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr rem(Expr x) {
        return ExprBinary.Op.REM.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this==x)
     * <p>
     * this and x must be expressions with the same arity, or both be integer
     * expressions
     */
    public final Expr equal(Expr x) {
        return ExprBinary.Op.EQUALS.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this &lt; x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr lt(Expr x) {
        return ExprBinary.Op.LT.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this &lt;= x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr lte(Expr x) {
        return ExprBinary.Op.LTE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this &gt; x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr gt(Expr x) {
        return ExprBinary.Op.GT.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this &gt;= x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr gte(Expr x) {
        return ExprBinary.Op.GTE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the integer expression (this &lt;&lt; x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr shl(Expr x) {
        return ExprBinary.Op.SHL.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the integer expression (this &gt;&gt;&gt; x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr shr(Expr x) {
        return ExprBinary.Op.SHR.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the integer expression (this &gt;&gt; x)
     * <p>
     * this and x must both be integer expressions
     */
    public final Expr sha(Expr x) {
        return ExprBinary.Op.SHA.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the formula (this in x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation or multiplicity constraint
     * <p>
     * this and x must have the same arity
     */
    public final Expr in(Expr x) {
        return ExprBinary.Op.IN.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression (this -> x) which can also be regarded as a
     * multiplicity constraint (this set->set x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr product(Expr x) {
        return ExprBinary.Op.ARROW.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this set->some x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr any_arrow_some(Expr x) {
        return ExprBinary.Op.ANY_ARROW_SOME.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this set->one x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr any_arrow_one(Expr x) {
        return ExprBinary.Op.ANY_ARROW_ONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this set->lone x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr any_arrow_lone(Expr x) {
        return ExprBinary.Op.ANY_ARROW_LONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this some->set x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr some_arrow_any(Expr x) {
        return ExprBinary.Op.SOME_ARROW_ANY.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this some->some x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr some_arrow_some(Expr x) {
        return ExprBinary.Op.SOME_ARROW_SOME.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this some->one x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr some_arrow_one(Expr x) {
        return ExprBinary.Op.SOME_ARROW_ONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this some->lone x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr some_arrow_lone(Expr x) {
        return ExprBinary.Op.SOME_ARROW_LONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this one->set x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr one_arrow_any(Expr x) {
        return ExprBinary.Op.ONE_ARROW_ANY.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this one->some x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr one_arrow_some(Expr x) {
        return ExprBinary.Op.ONE_ARROW_SOME.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this one->one x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr one_arrow_one(Expr x) {
        return ExprBinary.Op.ONE_ARROW_ONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this one->lone x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr one_arrow_lone(Expr x) {
        return ExprBinary.Op.ONE_ARROW_LONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this lone->set x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr lone_arrow_any(Expr x) {
        return ExprBinary.Op.LONE_ARROW_ANY.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this lone->some x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr lone_arrow_some(Expr x) {
        return ExprBinary.Op.LONE_ARROW_SOME.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this lone->one x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr lone_arrow_one(Expr x) {
        return ExprBinary.Op.LONE_ARROW_ONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this lone->lone x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr lone_arrow_lone(Expr x) {
        return ExprBinary.Op.LONE_ARROW_LONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the multiplicity constraint (this isSeq->lone x)
     * <p>
     * this must be a set or relation
     * <p>
     * x must be a set or relation
     */
    public final Expr isSeq_arrow_lone(Expr x) {
        return ExprBinary.Op.ISSEQ_ARROW_LONE.make(span().merge(x.span()), null, this, x);
    }

    /**
     * Returns the expression/integer/formula (this =&gt; x else y)
     * <p>
     * this must be a formula
     * <p>
     * x and y must both be expressions of the same arity, or both be integer
     * expressions, or both be formulas
     */
    public final Expr ite(Expr x, Expr y) {
        return ExprITE.make(Pos.UNKNOWN, this, x, y);
    }

    /**
     * Returns the formula (all...| this)
     * <p>
     * this must be a formula
     */
    public final Expr forAll(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.ALL.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the formula (no...| this)
     * <p>
     * this must be a formula
     */
    public final Expr forNo(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.NO.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the formula (lone...| this)
     * <p>
     * this must be a formula
     */
    public final Expr forLone(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.LONE.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the formula (one ...| this)
     * <p>
     * this must be a formula
     */
    public final Expr forOne(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.ONE.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the formula (some...| this)
     * <p>
     * this must be a formula
     */
    public final Expr forSome(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.SOME.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the comprehension expression {...|this}
     * <p>
     * this must be a formula
     * <p>
     * each declaration must be a "one-of" quantification over a unary set
     */
    public final Expr comprehensionOver(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.COMPREHENSION.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Returns the integer (sum...| this)
     * <p>
     * this must be an integer expression
     * <p>
     * each declaration must be a "one-of" quantification over a unary set
     */
    public final Expr sumOver(Decl firstDecl, Decl... moreDecls) throws Err {
        Pos p = firstDecl.span();
        for (Decl v : moreDecls)
            p = p.merge(v.span());
        return ExprQt.Op.SUM.make(p, null, Util.prepend(Util.asList(moreDecls), firstDecl), this);
    }

    /**
     * Return the multiplicity expression "some this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     */
    public final Expr someOf() {
        return ExprUnary.Op.SOMEOF.make(span(), this);
    }

    /**
     * Return a new declaration "v: some this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     * <p>
     * the label is only used for pretty-printing, and does not have to be unique
     */
    public final Decl someOf(String label) throws Err {
        Expr x = ExprUnary.Op.SOMEOF.make(span(), this);
        ExprVar v = ExprVar.make(x.span(), label, type);
        return new Decl(null, null, null, Arrays.asList(v), x);
    }

    /**
     * Return the multiplicity expression "lone this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     */
    public final Expr loneOf() {
        return ExprUnary.Op.LONEOF.make(span(), this);
    }

    /**
     * Return a new declaration "v: lone this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     * <p>
     * the label is only used for pretty-printing, and does not have to be unique
     */
    public final Decl loneOf(String label) throws Err {
        Expr x = ExprUnary.Op.LONEOF.make(span(), this);
        ExprVar v = ExprVar.make(x.span(), label, type);
        return new Decl(null, null, null, Arrays.asList(v), x);
    }

    /**
     * Return the multiplicity expression "one this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     */
    public final Expr oneOf() {
        return ExprUnary.Op.ONEOF.make(span(), this);
    }

    /**
     * Return a new declaration "v: one this"
     * <p>
     * this must be already fully typechecked, and must be a unary set
     * <p>
     * the label is only used for pretty-printing, and does not have to be unique
     */
    public final Decl oneOf(String label) throws Err {
        Expr x = ExprUnary.Op.ONEOF.make(span(), this);
        ExprVar v = ExprVar.make(x.span(), label, type);
        return new Decl(null, null, null, Arrays.asList(v), x);
    }

    /**
     * Return the multiplicity expression "set this"
     * <p>
     * this must be already fully typechecked, and must be a set or relation
     */
    public final Expr setOf() {
        return ExprUnary.Op.SETOF.make(span(), this);
    }

    /**
     * Return a new declaration "v: set this"
     * <p>
     * this must be already fully typechecked, and must be a set or relation
     * <p>
     * the label is only used for pretty-printing, and does not have to be unique
     */
    public final Decl setOf(String label) throws Err {
        Expr x = ExprUnary.Op.SETOF.make(span(), this);
        ExprVar v = ExprVar.make(x.span(), label, type);
        return new Decl(null, null, null, Arrays.asList(v), x);
    }

    /**
     * Returns the formula (not this)
     * <p>
     * this must be a formula
     */
    public final Expr not() {
        return ExprUnary.Op.NOT.make(span(), this);
    }

    /**
     * Returns the formula (no this)
     * <p>
     * this must be a set or a relation
     */
    public final Expr no() {
        return ExprUnary.Op.NO.make(span(), this);
    }

    /**
     * Returns the formula (some this)
     * <p>
     * this must be a set or a relation
     */
    public final Expr some() {
        return ExprUnary.Op.SOME.make(span(), this);
    }

    /**
     * Returns the formula (lone this)
     * <p>
     * this must be a set or a relation
     */
    public final Expr lone() {
        return ExprUnary.Op.LONE.make(span(), this);
    }

    /**
     * Returns the formula (one this)
     * <p>
     * this must be a set or a relation
     */
    public final Expr one() {
        return ExprUnary.Op.ONE.make(span(), this);
    }

    /**
     * Returns the expression (~this)
     * <p>
     * this must be a binary relation
     */
    public final Expr transpose() {
        return ExprUnary.Op.TRANSPOSE.make(span(), this);
    }

    /**
     * Returns the expression (*this)
     * <p>
     * this must be a binary relation
     */
    public final Expr reflexiveClosure() {
        return ExprUnary.Op.RCLOSURE.make(span(), this);
    }

    /**
     * Returns the expression (^this)
     * <p>
     * this must be a binary relation
     */
    public final Expr closure() {
        return ExprUnary.Op.CLOSURE.make(span(), this);
    }

    /**
     * Returns the integer expression (#this) truncated to the current integer
     * bitwidth.
     * <p>
     * this must be a set or a relation
     */
    public final Expr cardinality() {
        return ExprUnary.Op.CARDINALITY.make(span(), this);
    }

    /**
     * Returns the integer expression "int[this]"
     * <p>
     * this must be a unary set
     */
    public final Expr cast2int() {
        return ExprUnary.Op.CAST2INT.make(span(), this);
    }

    /**
     * Returns the singleton set "Int[this]"
     * <p>
     * this must be an integer expression
     */
    public final Expr cast2sigint() {
        return ExprUnary.Op.CAST2SIGINT.make(span(), this);
    }

    /**
     * Get the position where this expression is referring to or null if it is not
     * referring to anything.
     *
     */

    public void setReferenced(Clause clause) {
        this.referenced = clause;
    }

    public Clause referenced(Clause pos) {
        return referenced != null ? referenced : pos;
    }

    public Clause referenced() {
        return referenced;
    }
}
