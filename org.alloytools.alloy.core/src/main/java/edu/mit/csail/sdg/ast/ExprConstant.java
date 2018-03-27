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

import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

/** Immutable; represents a constant in the AST. */

public final class ExprConstant extends Expr {

    /** The type of constant. */
    public final Op     op;

    /**
     * If this node is a String constant, then this field stores the String, else
     * this field stores "".
     */
    public final String string;

    /**
     * If this node is a number constant, then this field stores the number, else
     * this field stores 0.
     */
    public final int    num;

    /**
     * Return the number if this node is a number constant, otherwise return 0.
     */
    public int num() {
        return num;
    }

    /** {@inheritDoc} */
    @Override
    public Pos span() {
        return pos;
    }

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            if (op == Op.NUMBER)
                out.append(num);
            else if (op == Op.STRING)
                out.append(string);
            else
                out.append(op);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            if (op == Op.NUMBER)
                out.append(num);
            else if (op == Op.STRING)
                out.append(string);
            else
                out.append(op);
            out.append('\n');
        }
    }

    /**
     * Constructs an ExprConstant node.
     *
     * @param pos - the original position in the file
     * @param op - the choice of which constant it is
     * @param num - the number (this argument is ignored if op!=NUMBER)
     */
    private ExprConstant(Pos pos, Op op, int num, String string) {
        super(pos, null, false, (op == Op.IDEN ? Type.make2(UNIV) : (op == Op.NEXT ? Type.make2(Sig.SIGINT) : (op == Op.TRUE || op == Op.FALSE ? Type.FORMULA : (op == Op.EMPTYNESS ? UNIV.type : (op == Op.STRING ? Sig.STRING.type : Type.smallIntType()))))), 0, 0, null);
        this.op = op;
        this.num = (op == Op.NUMBER ? num : 0);
        this.string = (op == Op.STRING ? string : "");
    }

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
        if (!(obj instanceof ExprConstant))
            return false;
        ExprConstant x = (ExprConstant) obj;
        if (op == Op.STRING)
            return op == x.op && string.equals(x.string);
        else
            return op == x.op && num == x.num;
    }

    /** The "TRUE" boolean value. */
    public static final Expr TRUE      = new ExprConstant(null, Op.TRUE, 0, "");

    /** The "FALSE" boolean value. */
    public static final Expr FALSE     = new ExprConstant(null, Op.FALSE, 0, "");

    /** The "iden" relation. */
    public static final Expr IDEN      = new ExprConstant(null, Op.IDEN, 0, "");

    /**
     * The smallest integer value allowed by the current bitwidth.
     */
    public static final Expr MIN       = new ExprConstant(null, Op.MIN, 0, "");

    /**
     * The largest integer value allowed by the current bitwidth.
     */
    public static final Expr MAX       = new ExprConstant(null, Op.MAX, 0, "");

    /**
     * The "next" relation relating each integer to its next larger integer.
     */
    public static final Expr NEXT      = new ExprConstant(null, Op.NEXT, 0, "");

    /** The "0" integer. */
    public static final Expr ZERO      = new ExprConstant(null, Op.NUMBER, 0, "");

    /** The "1" integer. */
    public static final Expr ONE       = new ExprConstant(null, Op.NUMBER, 1, "");

    /** The "emptyness" constant. */
    public static final Expr EMPTYNESS = new ExprConstant(null, Op.EMPTYNESS, 0, "");

    /** Constructs the integer "n" */
    public static Expr makeNUMBER(int n) {
        if (n == 0)
            return ZERO;
        if (n == 1)
            return ONE;
        return new ExprConstant(null, Op.NUMBER, n, "");
    }

    /** This class contains all possible constant types. */
    public enum Op {
                    /** true */
                    TRUE("true"),
                    /** false */
                    FALSE("false"),
                    /** the builtin "iden" relation */
                    IDEN("iden"),
                    /** the minimum integer constant */
                    MIN("min"),
                    /** the maximum integer constant */
                    MAX("max"),
                    /** the "next" relation between integers */
                    NEXT("next"),
                    /** the emptyness relation whose type is UNIV */
                    EMPTYNESS("none"),
                    /** a String constant */
                    STRING("STRING"),
                    /** an integer constant */
                    NUMBER("NUMBER");

        /** The constructor. */
        private Op(String label) {
            this.label = label;
        }

        /** The human readable label for this operator. */
        private final String label;

        /**
         * Makes an ExprConstant node
         *
         * @param pos - the original position in the source file (can be null if
         *            unknown)
         * @param number - the number (this argument is ignored if op!=NUMBER)
         */
        public final ExprConstant make(Pos pos, int number) {
            return new ExprConstant(pos, this, number, "");
        }

        /**
         * Makes an ExprConstant node
         *
         * @param pos - the original position in the source file (can be null if
         *            unknown)
         * @param string - the string (this argument is ignored if op!=STRING)
         */
        public final ExprConstant make(Pos pos, String string) {
            return new ExprConstant(pos, this, 0, string);
        }

        /** Returns the human readable label for this operator. */
        @Override
        public final String toString() {
            return label;
        }
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type type, Collection<ErrorWarning> warns) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        return 1;
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        switch (op) {
            case TRUE :
                return "<b>true</b>";
            case FALSE :
                return "<b>false</b>";
            case IDEN :
                return "<b>iden</b>";
            case MAX :
                return "<b>fun/max</b>";
            case MIN :
                return "<b>fun/min</b>";
            case NEXT :
                return "<b>fun/next</b>";
            case EMPTYNESS :
                return "<b>none</b>";
            case STRING :
                return "<b>\"" + string + "\"</b>";
        }
        return "<b>" + num + "</b>";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return new ArrayList<Browsable>(0);
    }
}
