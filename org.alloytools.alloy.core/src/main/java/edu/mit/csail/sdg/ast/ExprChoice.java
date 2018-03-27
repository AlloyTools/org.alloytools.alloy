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

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Immutable; represents an unresolved node that has several possibilities.
 */

public final class ExprChoice extends Expr {

    /**
     * The unmodifiable list of Expr(s) from that this ExprChoice can refer to.
     */
    public final ConstList<Expr>   choices;

    /**
     * The unmodifiable list of String(s) explaining where each choice came from.
     */
    public final ConstList<String> reasons;

    /** Caches the span() result. */
    private Pos                    span = null;

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        Pos p = span;
        if (p == null) {
            p = pos;
            for (Expr a : choices)
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
            out.append("<");
            for (Expr e : choices) {
                e.toString(out, -1);
                out.append(";");
            }
            out.append(">");
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("" + choices.size() + " choices with combined type=").append(type).append('\n');
        }
    }

    // ============================================================================================================//

    /**
     * Generate an appropriate error message in the case where there are no legal
     * choices.
     */
    private static Err complain(Pos pos, ConstList<Expr> choices) {
        StringBuilder sb = new StringBuilder("Name cannot be resolved; possible incorrect function/predicate call; " + "perhaps you used ( ) when you should have used [ ]\n");
        for (Expr x : choices) {
            pos = pos.merge(x.span());
            if (x instanceof ExprBadCall || x instanceof ExprBadJoin)
                sb.append('\n').append(x.errors.pick().msg);
        }
        return new ErrorType(pos, sb.toString());
    }

    // ============================================================================================================//

    /** Constructs an ExprChoice node. */
    private ExprChoice(Pos pos, ConstList<Expr> choices, ConstList<String> reasons, Type type, long weight) {
        super(pos, null, true, type, 0, weight, emptyListOfErrors.make(type == EMPTY ? complain(pos, choices) : null));
        this.choices = choices;
        this.reasons = reasons;
    }

    // ============================================================================================================//

    /** Construct an ExprChoice node. */
    public static Expr make(boolean ignoreIntFuns, Pos pos, ConstList<Expr> choices, ConstList<String> reasons) {
        if (choices.size() == 0)
            return new ExprBad(pos, "", new ErrorType(pos, "This expression failed to be typechecked."));
        if (choices.size() == 1 && choices.get(0).errors.isEmpty())
            return choices.get(0); // Shortcut
        if (ignoreIntFuns) {
            int n = choices.size();
            TempList<Expr> ch = new TempList<Expr>(n);
            TempList<String> rs = new TempList<String>(n);
            for (int i = 0; i < n; i++) {
                Expr e = choices.get(i);
                if (!((e instanceof ExprCall) && e.toString().startsWith("integer/"))) {
                    ch.add(e);
                    rs.add(reasons.get(i));
                }
            }
            return make(false, pos, ch.makeConst(), rs.makeConst());
        }
        Type type = EMPTY;
        boolean first = true;
        long weight = 0;
        for (Expr x : choices) {
            type = x.type.merge(type);
            if (first || weight > x.weight)
                if (x.type != EMPTY) {
                    weight = x.weight;
                    first = false;
                }
        }
        return new ExprChoice(pos, choices, reasons, type, weight);
    }

    // ============================================================================================================//

    /**
     * Resolve the list of choices, or return an ExprBad object containing the list
     * of unresolvable ambiguities.
     */
    private Expr resolveHelper(boolean firstPass, final Type t, List<Expr> choices, List<String> reasons, Collection<ErrorWarning> warns) {
        List<Expr> ch = new ArrayList<Expr>(choices.size());
        List<String> re = new ArrayList<String>(choices.size());
        // We first prefer exact matches
        for (int i = 0; i < choices.size(); i++) {
            Type tt = choices.get(i).type;
            if (/* [AM](t.is_int() && tt.is_int()) || */(t.is_bool && tt.is_bool) || t.intersects(tt)) {
                ch.add(choices.get(i));
                re.add(reasons.get(i));
            }
        }
        // If none, we try any legal matches
        if (ch.size() == 0) {
            for (int i = 0; i < choices.size(); i++)
                if (choices.get(i).type.hasCommonArity(t)) {
                    ch.add(choices.get(i));
                    re.add(reasons.get(i));
                }
        }
        // [AM]: TODO: anything special about this?
        // // If none, we try sigint->int
        // if (ch.size()==0 && Type.SIGINT2INT && t.is_int) {
        // for(int i=0; i<choices.size(); i++) if
        // (choices.get(i).type.intersects(SIGINT.type)) {
        // ch.add(choices.get(i).cast2int()); re.add(reasons.get(i)); }
        // }
        // // If none, we try int->sigint
        // if (ch.size()==0 && Type.INT2SIGINT && t.hasArity(1)) {
        // for(int i=0; i<choices.size(); i++) if (choices.get(i).type.is_int) {
        // ch.add(choices.get(i).cast2sigint()); re.add(reasons.get(i)); }
        // }
        // If too many, then keep the choices with the smallest weight
        if (ch.size() > 1) {
            List<Expr> ch2 = new ArrayList<Expr>(ch.size());
            List<String> re2 = new ArrayList<String>(ch.size());
            long w = 0;
            for (int i = 0; i < ch.size(); i++) {
                Expr c = ch.get(i);
                String r = re.get(i);
                if (ch2.size() > 0 && c.weight > w)
                    continue;
                else if (ch2.size() == 0 || c.weight < w) {
                    ch2.clear();
                    re2.clear();
                    w = c.weight;
                }
                ch2.add(c);
                re2.add(r);
            }
            ch = ch2;
            re = re2;
            // If still too many, but this is the first pass, then try to
            // resolve them all and try again
            if (firstPass && ch.size() > 1) {
                ch2 = new ArrayList<Expr>(ch.size());
                for (Expr c : ch)
                    ch2.add(c.resolve(t, null));
                return resolveHelper(false, t, ch2, re, warns);
            }
        }
        // If we are down to exactly 1 match, return it
        if (ch.size() == 1)
            return ch.get(0).resolve(t, warns);
        // If we are faced with 2 or more choices, but they all result in
        // emptyset-of-the-same-arity, then just return emptyset
        none: while (ch.size() > 1) {
            int arity = -1;
            for (Expr c : ch) {
                if (c.type.is_bool || c.type.is_int() || c.type.hasTuple())
                    break none;
                int a = c.type.arity();
                if (a < 1)
                    break none;
                if (arity < 0)
                    arity = a;
                else if (arity != a)
                    break none;
            }
            Expr ans = Sig.NONE;
            while (arity > 1) {
                ans = ans.product(Sig.NONE);
                arity--;
            }
            return ExprUnary.Op.NOOP.make(span(), ans);
        }
        // Otherwise, complain!
        String txt;
        if (ch.size() > 1) {
            txt = "\nThis name is ambiguous due to multiple matches:";
        } else {
            txt = "\nThis name cannot be resolved; its relevant type does not intersect with any of the following candidates:";
            re = reasons;
        }
        StringBuilder msg = new StringBuilder(txt);
        for (String r : re)
            msg.append('\n').append(r);
        return new ExprBad(pos, toString(), new ErrorType(pos, msg.toString()));
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warns) {
        if (errors.size() > 0)
            return this;
        else
            return resolveHelper(true, t, choices, reasons, warns);
    }

    // ============================================================================================================//

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = 1;
        for (Expr x : choices) {
            int tmp = x.getDepth();
            if (max < tmp)
                max = tmp;
        }
        return 1 + max;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        if (!errors.isEmpty())
            throw errors.pick();
        throw new ErrorType(span(), "This expression failed to be resolved.");
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>error</b> (parser or typechecker failed)";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return new ArrayList<Browsable>(0);
    }
}
