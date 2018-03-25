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

package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.VisitReturn;

/**
 * Immutable; this class rearranges the AST to promote as many clauses up to the
 * top level as possible (in order to get better precision unsat core results)
 */

final class ConvToConjunction extends VisitReturn<Expr> {

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprBinary x) throws Err {
        if (x.op == ExprBinary.Op.AND) {
            Expr a = visitThis(x.left);
            Expr b = visitThis(x.right);
            return a.and(b);
        }
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprQt x) throws Err {
        if (x.op == ExprQt.Op.ALL) {
            Expr s = x.sub.deNOP();
            if (s instanceof ExprBinary && ((ExprBinary) s).op == ExprBinary.Op.AND) {
                Expr a = visitThis(x.op.make(Pos.UNKNOWN, Pos.UNKNOWN, x.decls, ((ExprBinary) s).left));
                Expr b = visitThis(x.op.make(Pos.UNKNOWN, Pos.UNKNOWN, x.decls, ((ExprBinary) s).right));
                return a.and(b);
            }
        }
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprUnary x) throws Err {
        if (x.op == ExprUnary.Op.NOOP) {
            return visitThis(x.sub);
        }
        if (x.op == ExprUnary.Op.NOT) {
            Expr s = x.sub.deNOP();
            if (s instanceof ExprBinary && ((ExprBinary) s).op == ExprBinary.Op.OR) {
                Expr a = visitThis(((ExprBinary) s).left.not());
                Expr b = visitThis(((ExprBinary) s).right.not());
                return a.and(b);
            }
        }
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprList x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprCall x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprConstant x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprITE x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprLet x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(ExprVar x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(Sig x) {
        return x;
    }

    /** {@inheritDoc} */
    @Override
    public Expr visit(Field x) {
        return x;
    }
}
