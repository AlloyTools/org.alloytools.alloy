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

import static edu.mit.csail.sdg.ast.Type.EMPTY;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Type.ProductType;

/**
 * Immutable; represents an expression of the form (x OP y).
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (this.mult!=1)
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (this.mult==2 => this.op is one of the 17
 * arrow operators)
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (left.mult!=1)
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (left.mult==2 => this.op is one of the 17
 * arrow operators)
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (right.mult==1 => this.op==IN)
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (right.mult==2 => (this.op==IN || this.op is
 * one of the 17 arrow operators))
 */

public final class ExprBinary extends Expr {

    /** The binary operator. */
    public final Op   op;

    /** The left-hand-side expression. */
    public final Expr left;

    /** The right-hand-side expression. */
    public final Expr right;

    /** Caches the span() result. */
    private Pos       span = null;

    // ============================================================================================================//

    /** Constructs a new ExprBinary node. */
    private ExprBinary(Pos pos, Pos closingBracket, Op op, Expr left, Expr right, Type type, JoinableList<Err> errors) {
        super(pos, closingBracket, left.ambiguous || right.ambiguous, type, (op.isArrow && (left.mult == 2 || right.mult == 2 || op != Op.ARROW)) ? 2 : 0, left.weight + right.weight, errors);
        this.op = op;
        this.left = left;
        this.right = right;
    }

    // ============================================================================================================//

    /**
     * Returns true if we can determine the two expressions are equivalent; may
     * sometimes return false.
     */
    @Override
    public boolean isSame(Expr obj) {
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        if (obj == this)
            return true;
        if (!(obj instanceof ExprBinary))
            return false;
        ExprBinary x = (ExprBinary) obj;
        return op == x.op && left.isSame(x.left) && right.isSame(x.right);
    }

    // ============================================================================================================//

    /**
     * Convenience method that generates a type error with "msg" as the message, and
     * includes the left and right bounding types in the message.
     */
    private static ErrorType error(Pos pos, String msg, Expr left, Expr right) {
        return new ErrorType(pos, msg + "\nLeft type = " + left.type + "\nRight type = " + right.type);
    }

    // ============================================================================================================//

    /**
     * Convenience method that generates a type warning with "msg" as the message,
     * and includes the left and right bounding types in the message.
     */
    private ErrorWarning warn(String msg) {
        return new ErrorWarning(pos, msg + "\nLeft type = " + Type.removesBoolAndInt(left.type) + "\nRight type = " + Type.removesBoolAndInt(right.type));
    }

    // ============================================================================================================//

    /**
     * Convenience method that generates a type warning with "msg" as the message,
     * and includes the parent's relevance type, as well as the left and right
     * bounding types in the message.
     */
    private ErrorWarning warn(String msg, Type parent) {
        return new ErrorWarning(pos, msg + "\nParent's relevant type = " + Type.removesBoolAndInt(parent) + "\nLeft type = " + Type.removesBoolAndInt(left.type) + "\nRight type = " + Type.removesBoolAndInt(right.type));
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        if (p == null)
            span = (p = pos.merge(closingBracket).merge(right.span()).merge(left.span()));
        return p;
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            if (op == Op.ISSEQ_ARROW_LONE)
                out.append("seq ");
            else {
                left.toString(out, -1);
                out.append(' ').append(op).append(' ');
            }
            right.toString(out, -1);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append(op).append(" with type=").append(type).append('\n');
            left.toString(out, indent + 2);
            right.toString(out, indent + 2);
        }
    }

    // ============================================================================================================//

    /** This class contains all possible binary operators. */
    public static enum Op {
                           /** -&gt; */
                           ARROW("->", true),
                           /** -&gt;some */
                           ANY_ARROW_SOME("->some", true),
                           /** -&gt;one */
                           ANY_ARROW_ONE("->one", true),
                           /** -&gt;lone */
                           ANY_ARROW_LONE("->lone", true),
                           /** some-&gt; */
                           SOME_ARROW_ANY("some->", true),
                           /** some-&gt;some */
                           SOME_ARROW_SOME("some->some", true),
                           /** some-&gt;one */
                           SOME_ARROW_ONE("some->one", true),
                           /** some-&gt;lone */
                           SOME_ARROW_LONE("some->lone", true),
                           /** one-&gt; */
                           ONE_ARROW_ANY("one->", true),
                           /** one-&gt;some */
                           ONE_ARROW_SOME("one->some", true),
                           /** one-&gt;one */
                           ONE_ARROW_ONE("one->one", true),
                           /** one-&gt;lone */
                           ONE_ARROW_LONE("one->lone", true),
                           /** lone-&gt; */
                           LONE_ARROW_ANY("lone->", true),
                           /** lone-&gt;some */
                           LONE_ARROW_SOME("lone->some", true),
                           /** lone-&gt;one */
                           LONE_ARROW_ONE("lone->one", true),
                           /** lone-&gt;lone */
                           LONE_ARROW_LONE("lone->lone", true),
                           /** isSeq-&gt;lone */
                           ISSEQ_ARROW_LONE("isSeq->lone", true),
                           /** . */
                           JOIN(".", false),
                           /** &lt;: */
                           DOMAIN("<:", false),
                           /** :&gt; */
                           RANGE(":>", false),
                           /** &amp; */
                           INTERSECT("&", false),
                           /** ++ */
                           PLUSPLUS("++", false),
                           /** set union */
                           PLUS("+", false),
                           /** int + */
                           IPLUS("@+", false),
                           /** set diff */
                           MINUS("-", false),
                           /** int - */
                           IMINUS("@-", false),
                           /** multiply */
                           MUL("*", false),
                           /** divide */
                           DIV("/", false),
                           /** remainder */
                           REM("%", false),
                           /** = */
                           EQUALS("=", false),
                           /** != */
                           NOT_EQUALS("!=", false),
                           /** =&gt; */
                           IMPLIES("=>", false),
                           /** &lt; */
                           LT("<", false),
                           /** =&lt; */
                           LTE("<=", false),
                           /** &gt; */
                           GT(">", false),
                           /** &gt;= */
                           GTE(">=", false),
                           /** !&lt; */
                           NOT_LT("!<", false),
                           /** !=&lt; */
                           NOT_LTE("!<=", false),
                           /** !&gt; */
                           NOT_GT("!>", false),
                           /** !&gt;= */
                           NOT_GTE("!>=", false),
                           /** &lt;&lt; */
                           SHL("<<", false),
                           /** &gt;&gt; */
                           SHA(">>", false),
                           /** &gt;&gt;&gt; */
                           SHR(">>>", false),
                           /** in */
                           IN("in", false),
                           /** !in */
                           NOT_IN("!in", false),
                           /** &amp;&amp; */
                           AND("&&", false),
                           /** || */
                           OR("||", false),
                           /** &lt;=&gt; */
                           IFF("<=>", false);

        /**
         * The constructor.
         *
         * @param label - the label (for printing debugging messages)
         * @param isArrow - true if this operator is one of the 17 arrow operators
         */
        private Op(String label, boolean isArrow) {
            this.label = label;
            this.isArrow = isArrow;
        }

        /** The human readable label for this operator. */
        private final String label;

        /**
         * True if and only if this operator is the Cartesian product "->", a "seq"
         * multiplicity, or is a multiplicity arrow of the form "?->?".
         */
        public final boolean isArrow;

        /**
         * Constructs a new ExprBinary node.
         *
         * @param pos - the original position in the source file (can be null if
         *            unknown)
         * @param left - the left hand side expression
         * @param right - the right hand side expression
         */
        public final Expr make(Pos pos, Pos closingBracket, Expr left, Expr right) {
            switch (this) {
                case AND :
                    return ExprList.makeAND(pos, closingBracket, left, right);
                case OR :
                    return ExprList.makeOR(pos, closingBracket, left, right);
                case DOMAIN : {
                    // Special optimization
                    Expr f = right.deNOP();
                    if (f instanceof Field && ((Field) f).sig == left.deNOP())
                        return right;
                    break;
                }
                case MUL :
                case DIV :
                case REM :
                case LT :
                case LTE :
                case GT :
                case GTE :
                case SHL :
                case SHR :
                case SHA :
                case NOT_LT :
                case NOT_GT :
                case NOT_LTE :
                case NOT_GTE : {
                    left = left.typecheck_as_int();
                    right = right.typecheck_as_int();
                    break;
                }
                case IFF :
                case IMPLIES : {
                    left = left.typecheck_as_formula();
                    right = right.typecheck_as_formula();
                    break;
                }
                case IPLUS :
                case IMINUS : {
                    left = left.typecheck_as_int();
                    right = right.typecheck_as_int();
                    break;
                }
                case PLUS :
                case MINUS :
                case EQUALS :
                case NOT_EQUALS : {
                    // [AM]: these are always relational operators now, so no
                    // casts
                    // Type a=left.type, b=right.type;
                    // if (a.hasCommonArity(b) || (a.is_int && b.is_int)) break;
                    // if (Type.SIGINT2INT) {
                    // if (a.is_int && b.intersects(SIGINT.type)) {
                    // right=right.cast2int(); break; }
                    // if (b.is_int && a.intersects(SIGINT.type)) {
                    // left=left.cast2int(); break; }
                    // }
                    // if (Type.INT2SIGINT) {
                    // if (a.is_int && b.hasArity(1)) { left=left.cast2sigint();
                    // break; }
                    // if (b.is_int && a.hasArity(1)) {
                    // right=right.cast2sigint(); break; }
                    // }
                    break;
                }
                default : {
                    left = left.typecheck_as_set();
                    right = right.typecheck_as_set();
                }
            }
            Err e = null;
            Type type = EMPTY;
            JoinableList<Err> errs = left.errors.make(right.errors);
            if (errs.isEmpty())
                switch (this) {
                    case LT :
                    case LTE :
                    case GT :
                    case GTE :
                    case NOT_LT :
                    case NOT_LTE :
                    case NOT_GT :
                    case NOT_GTE :
                    case AND :
                    case OR :
                    case IFF :
                    case IMPLIES :
                        type = Type.FORMULA;
                        break;
                    case MUL :
                    case DIV :
                    case REM :
                    case SHL :
                    case SHR :
                    case SHA :
                        type = Type.smallIntType();
                        break;
                    case PLUSPLUS :
                        type = left.type.unionWithCommonArity(right.type);
                        if (type == EMPTY)
                            e = error(pos, "++ can be used only between two expressions of the same arity.", left, right);
                        break;
                    case PLUS :
                    case MINUS :
                    case EQUALS :
                    case NOT_EQUALS :
                        if (this == EQUALS || this == NOT_EQUALS) {
                            if (left.type.hasCommonArity(right.type) || (left.type.is_int() && right.type.is_int())) {
                                type = Type.FORMULA;
                                break;
                            }
                        } else {
                            type = (this == PLUS ? left.type.unionWithCommonArity(right.type) : left.type.pickCommonArity(right.type));
                            if (type != EMPTY)
                                break;
                        }
                        e = error(pos, this + " can be used only between 2 expressions of the same arity, or between 2 integer expressions.", left, right);
                        break;
                    case IPLUS :
                    case IMINUS :
                        type = Type.smallIntType();
                        break;
                    case IN :
                    case NOT_IN :
                        type = (left.type.hasCommonArity(right.type)) ? Type.FORMULA : EMPTY;
                        if (type == EMPTY)
                            e = error(pos, this + " can be used only between 2 expressions of the same arity.", left, right);
                        break;
                    case JOIN :
                        type = left.type.join(right.type);
                        if (type == EMPTY)
                            return ExprBadJoin.make(pos, closingBracket, left, right);
                        break;
                    case DOMAIN :
                        type = right.type.domainRestrict(left.type);
                        if (type == EMPTY)
                            e = new ErrorType(left.span(), "This must be a unary set, but instead it has the following possible type(s):\n" + left.type);
                        break;
                    case RANGE :
                        type = left.type.rangeRestrict(right.type);
                        if (type == EMPTY)
                            e = new ErrorType(right.span(), "This must be a unary set, but instead it has the following possible type(s):\n" + right.type);
                        break;
                    case INTERSECT :
                        type = left.type.intersect(right.type);
                        if (type == EMPTY)
                            e = error(pos, "& can be used only between 2 expressions of the same arity.", left, right);
                        break;
                    default :
                        type = left.type.product(right.type);
                }
            if ((isArrow && left.mult == 1) || (!isArrow && left.mult != 0))
                errs = errs.make(new ErrorSyntax(left.span(), "Multiplicity expression not allowed here."));
            if ((isArrow && right.mult == 1) || (!isArrow && this != Op.IN && right.mult != 0))
                errs = errs.make(new ErrorSyntax(right.span(), "Multiplicity expression not allowed here."));
            return new ExprBinary(pos, closingBracket, this, left, right, type, errs.make(e));
        }

        /** Returns the human readable label for this operator. */
        @Override
        public final String toString() {
            return label;
        }

        /**
         * Returns the human readable label already encoded for HTML
         */
        public final String toHTML() {
            return "<b>" + Util.encode(label) + "</b>";
        }
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type p, Collection<ErrorWarning> warns) {
        if (errors.size() > 0)
            return this;
        ErrorWarning w = null;
        Type a = left.type, b = right.type;
        switch (op) {
            case MUL :
            case DIV :
            case REM :
            case LT :
            case LTE :
            case GT :
            case GTE :
            case SHL :
            case SHR :
            case SHA :
            case NOT_LTE :
            case NOT_GTE :
            case NOT_LT :
            case NOT_GT : {
                a = (b = Type.smallIntType());
                break;
            }
            case AND :
            case OR :
            case IFF :
            case IMPLIES : {
                a = (b = Type.FORMULA);
                break;
            }
            case EQUALS :
            case NOT_EQUALS : {
                p = a.intersect(b);
                if (p.hasTuple()) {
                    a = p;
                    b = p;
                } else {
                    a = a.pickCommonArity(b);
                    b = b.pickCommonArity(a);
                }
                // [AM]
                // if (left.type.is_int() && right.type.is_int()) {
                // a=Type.makeInt(a); b=Type.makeInt(b);
                // } else
                if (warns == null) {
                    break;
                } else if (left.type.hasTuple() && right.type.hasTuple() && !(left.type.intersects(right.type))) {
                    w = warn("== is redundant, because the left and right expressions are always disjoint.");
                } else if (left.isSame(right)) {
                    w = warn("== is redundant, because the left and right expressions always have the same value.");
                }
                break;
            }
            case IN :
            case NOT_IN : {
                a = a.pickCommonArity(b);
                b = b.intersect(a);
                if (warns == null)
                    break;
                if (left.type.hasNoTuple() && right.type.hasNoTuple())
                    w = warn("Subset operator is redundant, because both subexpressions are always empty.");
                else if (left.type.hasNoTuple())
                    w = warn("Subset operator is redundant, because the left subexpression is always empty.");
                else if (right.type.hasNoTuple())
                    w = warn("Subset operator is redundant, because the right subexpression is always empty.");
                else if (b.hasNoTuple())
                    w = warn("Subset operator is redundant, because the left and right subexpressions are always disjoint.");
                else if (left.isSame(right))
                    w = warn("Subset operator is redundant, because the left and right expressions always have the same value.");
                break;
            }
            case INTERSECT : {
                a = a.intersect(p);
                b = b.intersect(p);
                if (warns != null && type.hasNoTuple())
                    w = warn("& is irrelevant because the two subexpressions are always disjoint.");
                break;
            }
            case IPLUS :
            case IMINUS : {
                a = Type.smallIntType();
                b = Type.smallIntType();
                break;
            }
            case PLUSPLUS :
            case PLUS : {
                a = a.intersect(p);
                b = b.intersect(p);
                // [AM]
                // if (op==Op.PLUS && p.is_int()) { a=Type.makeInt(a);
                // b=Type.makeInt(b); }
                if (warns == null)
                    break;
                if (a == EMPTY && b == EMPTY)
                    w = warn(this + " is irrelevant since both subexpressions are redundant.", p);
                else if (a == EMPTY)
                    w = warn(this + " is irrelevant since the left subexpression is redundant.", p);
                else if (b == EMPTY || (op == Op.PLUSPLUS && !right.type.canOverride(left.type)))
                    w = warn(this + " is irrelevant since the right subexpression is redundant.", p);
                break;
            }
            case MINUS : {
                a = p;
                b = p.intersect(b);
                // [AM]
                // if (p.is_int()) {
                // a=Type.makeInt(a); b=Type.makeInt(b);
                // } else
                if (warns != null && (type.hasNoTuple() || b.hasNoTuple())) {
                    w = warn("- is irrelevant since the right expression is redundant.", p);
                }
                break;
            }
            case JOIN : {
                if (warns != null && type.hasNoTuple())
                    w = warn("The join operation here always yields an empty set.");
                a = (b = EMPTY);
                for (ProductType aa : left.type)
                    for (ProductType bb : right.type)
                        if (p.hasArity(aa.arity() + bb.arity() - 2)) {
                            PrimSig j = aa.get(aa.arity() - 1).intersect(bb.get(0));
                            if (j != Sig.NONE)
                                for (ProductType cc : p.intersect(aa.join(bb)))
                                    if (!cc.isEmpty()) {
                                        List<PrimSig> v = new ArrayList<PrimSig>(cc.arity() + 1);
                                        for (int i = 0; i < cc.arity(); i++)
                                            v.add(cc.get(i));
                                        v.add(aa.arity() - 1, j);
                                        a = a.merge(Type.make(v, 0, aa.arity()));
                                        b = b.merge(Type.make(v, aa.arity() - 1, v.size()));
                                    }
                        }
                if (a == EMPTY || b == EMPTY) { // Continue the best we can; we
                                               // should have issued a
                                               // relevance warning elsewhere
                                               // already.
                    a = (b = EMPTY);
                    for (ProductType aa : left.type)
                        for (ProductType bb : right.type)
                            if (p.hasArity(aa.arity() + bb.arity() - 2) && aa.get(aa.arity() - 1).intersects(bb.get(0))) {
                                a = a.merge(aa);
                                b = b.merge(bb);
                            }
                }
                if (a == EMPTY || b == EMPTY) { // Continue the best we can; we
                                               // should have issued a
                                               // relevance warning elsewhere
                                               // already.
                    a = (b = EMPTY);
                    for (ProductType aa : left.type)
                        for (ProductType bb : right.type)
                            if (p.hasArity(aa.arity() + bb.arity() - 2)) {
                                a = a.merge(aa);
                                b = b.merge(bb);
                            }
                }
                break;
            }
            case DOMAIN : {
                // leftType' = {r1 | r1 in leftType and there exists r2 in
                // rightType such that r1<:r2 in parentType}
                // rightType' = {r2 | r2 in rightType and there exists r1 in
                // leftType such that r1<:r2 in parentType}
                if (warns != null && type.hasNoTuple())
                    w = warn("<: is irrelevant because the result is always empty.");
                Type leftType = EMPTY, rightType = EMPTY;
                for (ProductType aa : a)
                    if (aa.arity() == 1)
                        for (ProductType bb : b)
                            if (p.hasArity(bb.arity()))
                                for (ProductType cc : p.intersect(bb.columnRestrict(aa.get(0), 0)))
                                    if (!cc.isEmpty()) {
                                        leftType = leftType.merge(cc, 0, 1);
                                        rightType = rightType.merge(cc);
                                    }
                if (leftType == EMPTY || rightType == EMPTY) { // We try to
                                                              // proceed the
                                                              // best we can
                    leftType = a.extract(1);
                    rightType = b.pickCommonArity(p);
                }
                a = leftType;
                b = rightType;
                break;
            }
            case RANGE : {
                // leftType' = {r1 | r1 in leftType and there exists r2 in
                // rightType such that r1:>r2 in parentType}
                // rightType' = {r2 | r2 in rightType and there exists r1 in
                // leftType such that r1:>r2 in parentType}
                if (warns != null && type.hasNoTuple())
                    w = warn(":> is irrelevant because the result is always empty.");
                Type leftType = EMPTY, rightType = EMPTY;
                for (ProductType bb : b)
                    if (bb.arity() == 1)
                        for (ProductType aa : a)
                            if (p.hasArity(aa.arity()))
                                for (ProductType cc : p.intersect(aa.columnRestrict(bb.get(0), aa.arity() - 1)))
                                    if (!cc.isEmpty()) {
                                        leftType = leftType.merge(cc);
                                        rightType = rightType.merge(cc, cc.arity() - 1, cc.arity());
                                    }
                if (leftType == EMPTY || rightType == EMPTY) { // We try to
                                                              // proceed the
                                                              // best we can
                    leftType = a.pickCommonArity(p);
                    rightType = b.extract(1);
                }
                a = leftType;
                b = rightType;
                break;
            }
            default : {
                // leftType' == {r1 | r1 in leftType and there exists r2 in
                // rightType such that r1->r2 in parentType}
                // rightType' == {r2 | r2 in rightType and there exists r1 in
                // leftType such that r1->r2 in parentType}
                if (warns == null) {
                    // do nothing
                } else if (a.hasTuple()) {
                    if (b.hasNoTuple())
                        w = warn("The left expression of -> is irrelevant because the right expression is always empty.");
                } else {
                    if (b.hasTuple())
                        w = warn("The right expression of -> is irrelevant because the left expression is always empty.");
                }
                Type leftType = EMPTY, rightType = EMPTY;
                for (ProductType aa : a)
                    if (!aa.isEmpty())
                        for (ProductType bb : b)
                            if (!bb.isEmpty() && p.hasArity(aa.arity() + bb.arity()))
                                for (ProductType cc : p.intersect(aa.product(bb)))
                                    if (!cc.isEmpty()) {
                                        leftType = leftType.merge(cc, 0, aa.arity());
                                        rightType = rightType.merge(cc, aa.arity(), cc.arity());
                                    }
                // We try to proceed the best we can; we should have issued a
                // relevance warning already.
                if (leftType == EMPTY || rightType == EMPTY) {
                    leftType = a;
                    rightType = b;
                }
                a = leftType;
                b = rightType;
            }
        }
        Expr left = this.left.resolve(a, warns);
        Expr right = this.right.resolve(b, warns);
        if (w != null)
            warns.add(w);
        return (left == this.left && right == this.right) ? this : op.make(pos, closingBracket, left, right);
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int a = left.getDepth(), b = right.getDepth();
        if (a >= b)
            return 1 + a;
        else
            return 1 + b;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return op.toHTML() + " <i>" + type + "</i>";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return Util.asList(left, right);
    }
}
