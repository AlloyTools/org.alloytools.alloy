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

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents disjoint[] or pred/totalOrder[] or (... and ... and ..)
 * and other similar list of arguments.
 * <p>
 * <b>Invariant:</b> type!=EMPTY => (all x:args | x.mult==0)
 */

public final class ExprList extends Expr {


    /** This class contains all possible builtin predicates. */
    public static enum Op {
                           /**
                            * DISJOINT (meaning the argument relations are all disjoint)
                            */
                           DISJOINT,
                           /**
                            * TOTALORDER (meaning it's a total order over the arguments)
                            */
                           TOTALORDER,
                           /**
                            * AND (meaning the logical conjunction of all arguments)
                            */
                           AND,
                           /** OR (meaning the logical disjunction of all arguments) */
                           OR
    }

    /** The builtin operator. */
    public final Op              op;

    /** The unmodifiable list of arguments. */
    public final ConstList<Expr> args;

    /** Caches the span() result. */
    private Pos                  span = null;

    /**
     * The positions where implicit in-line conjunctions occurred with an associated
     * message.
     */
    public final Map<Pos,String> implicits;

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        if (p == null) {
            p = pos.merge(closingBracket);
            for (Expr a : args)
                p = p.merge(a.span());
            span = p;
        }
        return p;
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(op).append("[");
            for (int i = 0; i < args.size(); i++) {
                if (i > 0)
                    out.append(", ");
                args.get(i).toString(out, -1);
            }
            out.append(']');
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append(op).append("[] with type=").append(type).append('\n');
            for (Expr a : args) {
                a.toString(out, indent + 2);
            }
        }
    }

    // ============================================================================================================//

    /** Constructs an ExprList node. */
    private ExprList(Pos pos, Pos closingBracket, Op op, boolean ambiguous, ConstList<Expr> args, long weight, JoinableList<Err> errs, Map<Pos,String> implicits) {
        super(pos, closingBracket, ambiguous, Type.FORMULA, 0, weight, errs);
        this.op = op;
        this.args = args;
        this.implicits = implicits;
    }

    // ============================================================================================================//

    /**
     * Add expr to list, in a way that flattens the conjunctions as much as possible
     * (for better unsat core). Registers implicit in-line conjunctions.
     */
    private static Map<Pos,String> addAND(TempList<Expr> list, Expr expr) {
        Map<Pos,String> implicits = new HashMap<Pos,String>();
        Expr x = expr.deNOP();
        if (x.isSame(ExprConstant.TRUE))
            return implicits;
        if (x instanceof ExprBinary && ((ExprBinary) x).op == ExprBinary.Op.AND) {
            implicits.putAll(addAND(list, ((ExprBinary) x).left));
            implicits.putAll(addAND(list, ((ExprBinary) x).right));
            return implicits;
        }
        if (x instanceof ExprList && ((ExprList) x).op == ExprList.Op.AND) {
            implicits.putAll(((ExprList) x).implicits);
            for (Expr y : ((ExprList) x).args)
                implicits.putAll(addAND(list, y));
            return implicits;
        }
        list.add(expr);
        return implicits;
    }

    /**
     * Add expr to list, in a way that flattens the disjunctions as much as possible
     * (for better unsat core).
     */
    private static void addOR(TempList<Expr> list, Expr expr) {
        Expr x = expr.deNOP();
        if (x.isSame(ExprConstant.FALSE))
            return;
        if (x instanceof ExprBinary && ((ExprBinary) x).op == ExprBinary.Op.OR) {
            addOR(list, ((ExprBinary) x).left);
            addOR(list, ((ExprBinary) x).right);
            return;
        }
        if (x instanceof ExprList && ((ExprList) x).op == ExprList.Op.OR) {
            for (Expr y : ((ExprList) x).args)
                addOR(list, y);
            return;
        }
        list.add(expr);
    }

    public static ExprList make(Pos pos, Pos closingBracket, Op op, List< ? extends Expr> args) {
        return make(pos, closingBracket, op, args, null);
    }

    /**
     * Generates a call to a builtin predicate
     *
     * @param implicit
     */
    public static ExprList make(Pos pos, Pos closingBracket, Op op, List< ? extends Expr> args, Entry<Pos,String> implicit) {
        boolean ambiguous = false;
        JoinableList<Err> errs = emptyListOfErrors;
        TempList<Expr> newargs = new TempList<Expr>(args.size());
        long weight = 0;
        Type commonArity = null;
        Map<Pos,String> implicits = new HashMap<Pos,String>();
        if (implicit != null)
            implicits.put(implicit.getKey(), implicit.getValue());
        for (int i = 0; i < args.size(); i++) {
            Expr a = (op == Op.AND || op == Op.OR) ? args.get(i).typecheck_as_formula() : args.get(i).typecheck_as_set();
            ambiguous = ambiguous || a.ambiguous;
            weight = weight + a.weight;
            if (a.mult != 0)
                errs = errs.make(new ErrorSyntax(a.span(), "Multiplicity expression not allowed here."));
            if (!a.errors.isEmpty())
                errs = errs.make(a.errors);
            else if (commonArity == null)
                commonArity = a.type;
            else
                commonArity = commonArity.pickCommonArity(a.type);
            if (op == Op.AND)
                implicits.putAll(addAND(newargs, a));
            else if (op == Op.OR)
                addOR(newargs, a);
            else
                newargs.add(a);
        }
        if (op == Op.TOTALORDER) {
            if (newargs.size() != 3) {
                errs = errs.make(new ErrorSyntax(pos, "The builtin pred/totalOrder[] predicate must be called with exactly three arguments."));
            } else if (errs.isEmpty()) {
                if (!newargs.get(0).type.hasArity(1))
                    errs = errs.make(new ErrorType(pos, "The first argument to pred/totalOrder must be unary."));
                if (!newargs.get(1).type.hasArity(1))
                    errs = errs.make(new ErrorType(pos, "The second argument to pred/totalOrder must be unary."));
                if (!newargs.get(2).type.hasArity(2))
                    errs = errs.make(new ErrorType(pos, "The third argument to pred/totalOrder must be binary."));
            }
        }
        if (op == Op.DISJOINT) {
            if (newargs.size() < 2)
                errs = errs.make(new ErrorSyntax(pos, "The builtin disjoint[] predicate must be called with at least two arguments."));
            if (commonArity == EMPTY)
                errs = errs.make(new ErrorType(pos, "The builtin predicate disjoint[] cannot be used among expressions of different arities."));
        }
        return new ExprList(pos, closingBracket, op, ambiguous, newargs.makeConst(), weight, errs, implicits);
    }

    /** Generates the expression (arg1 and arg2) */
    public static ExprList makeAND(Pos pos, Pos closingBracket, Expr a, Expr b) {
        TempList<Expr> list = new TempList<Expr>(2);
        list.add(a);
        list.add(b);
        Entry<Pos,String> implicit = null;
        if (pos == null && a.span().y2 == b.span().y) {
            Browsable lf = a;
            if (a instanceof ExprList)
                lf = ((ExprList) a).args.get(((ExprList) a).args.size() - 1);
            implicit = new AbstractMap.SimpleEntry<Pos,String>(new Pos(a.span().filename, a.span().x2, a.span().y2, b.span().x, b.span().y), "(" + lf + ") and (" + b + ")");
        }
        ExprList lst = make(pos, closingBracket, Op.AND, list.makeConst(), implicit);
        return lst;
    }

    /** Generates the expression (arg1 || arg2) */
    public static ExprList makeOR(Pos pos, Pos closingBracket, Expr a, Expr b) {
        TempList<Expr> list = new TempList<Expr>(2);
        list.add(a);
        list.add(b);
        return make(pos, closingBracket, Op.OR, list.makeConst());
    }

    /**
     * Generates the expression pred/totalOrder[arg1, args2, arg3...]
     */
    public static ExprList makeTOTALORDER(Pos pos, Pos closingBracket, List< ? extends Expr> args) {
        return make(pos, closingBracket, Op.TOTALORDER, args);
    }

    /** Generates the expression disj[arg1, args2, arg3...] */
    public static ExprList makeDISJOINT(Pos pos, Pos closingBracket, List< ? extends Expr> args) {
        return make(pos, closingBracket, Op.DISJOINT, args);
    }

    /**
     * Return a new ExprList object that is the same as this one except with one
     * additional argument.
     */
    public ExprList addArg(Expr x) {
        List<Expr> args = new ArrayList<Expr>(this.args);
        args.add(x);
        return make(pos, closingBracket, op, args);
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type p, Collection<ErrorWarning> warns) {
        TempList<Expr> newargs = new TempList<Expr>(args.size());
        boolean changed = false;
        if (errors.size() > 0)
            return this;
        if (op == Op.AND || op == Op.OR) {
            for (int i = 0; i < args.size(); i++) {
                Expr x = args.get(i);
                Expr y = x.resolve(Type.FORMULA, warns).typecheck_as_formula();
                if (x != y)
                    changed = true;
                newargs.add(y);
            }
        }
        if (op == Op.DISJOINT) {
            for (int i = 0; i < args.size(); i++) {
                if (i == 0)
                    p = Type.removesBoolAndInt(args.get(i).type);
                else
                    p = p.unionWithCommonArity(args.get(i).type);
            }
            for (int i = 0; i < args.size(); i++) {
                Expr x = args.get(i);
                Expr y = x.resolve(p, warns).typecheck_as_set();
                if (x != y)
                    changed = true;
                newargs.add(y);
            }
        }
        if (op == Op.TOTALORDER) {
            Type t = args.get(0).type.pickUnary();
            Expr a = args.get(0).resolve(t, warns).typecheck_as_set();
            Expr b = args.get(1).resolve(t, warns).typecheck_as_set();
            Expr c = args.get(2).resolve(t.product(t), warns).typecheck_as_set();
            changed = (a != args.get(0) || b != args.get(1) || c != args.get(2));
            newargs.add(a).add(b).add(c);
        }
        return changed ? make(pos, closingBracket, op, newargs.makeConst()) : this;
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = 1;
        for (Expr x : args) {
            int tmp = x.getDepth();
            if (max < tmp)
                max = tmp;
        }
        return 1 + max;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>" + op + " [ ]</b>";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return args;
    }
}
