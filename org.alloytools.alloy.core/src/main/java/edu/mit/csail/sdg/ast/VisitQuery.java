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

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Sig.Field;

/**
 * This abstract class implements a Query visitor that walks over an Expr and
 * its subnodes. <br>
 * As soon as one of the node returns a nonnull value,the nonnull value will be
 * propagated to be the output of this visitor.
 * <p>
 * This default implementation will return null on all the leaf Expr nodes and
 * thus the final answer will be null. <br>
 * To implement a particular query, you need to extend this class.
 */

public abstract class VisitQuery<T> extends VisitReturn<T> {

    /** Constructs a VisitQuery object. */
    public VisitQuery() {}

    /**
     * Visits an ExprBinary node (A OP B) by calling accept() on A then B.
     */
    @Override
    public T visit(ExprBinary x) throws Err {
        T ans = x.left.accept(this);
        if (ans == null)
            ans = x.right.accept(this);
        return ans;
    }

    /**
     * Visits an ExprList node F[X1,X2,X3..] by calling accept() on X1, X2, X3...
     */
    @Override
    public T visit(ExprList x) throws Err {
        for (Expr y : x.args) {
            T ans = y.accept(this);
            if (ans != null)
                return ans;
        }
        return null;
    }

    /**
     * Visits an ExprCall node F[X1,X2,X3..] by calling accept() on X1, X2, X3...
     */
    @Override
    public T visit(ExprCall x) throws Err {
        for (Expr y : x.args) {
            T ans = y.accept(this);
            if (ans != null)
                return ans;
        }
        return null;
    }

    /**
     * Visits an ExprConstant node (this default implementation simply returns null)
     */
    @Override
    public T visit(ExprConstant x) throws Err {
        return null;
    }

    /**
     * Visits an ExprITE node (C => X else Y) by calling accept() on C, X, then Y.
     */
    @Override
    public T visit(ExprITE x) throws Err {
        T ans = x.cond.accept(this);
        if (ans == null)
            ans = x.left.accept(this);
        if (ans == null)
            ans = x.right.accept(this);
        return ans;
    }

    /**
     * Visits an ExprLet node (let a=x | y) by calling accept() on "a", "x", then
     * "y".
     */
    @Override
    public T visit(ExprLet x) throws Err {
        T ans = x.var.accept(this);
        if (ans == null)
            ans = x.expr.accept(this);
        if (ans == null)
            ans = x.sub.accept(this);
        return ans;
    }

    /**
     * Visits an ExprQt node (all a,b,c:X1, d,e,f:X2... | F) by calling accept() on
     * a,b,c,X1,d,e,f,X2... then on F.
     */
    @Override
    public T visit(ExprQt x) throws Err {
        for (Decl d : x.decls) {
            for (ExprHasName v : d.names) {
                T ans = v.accept(this);
                if (ans != null)
                    return ans;
            }
            T ans = d.expr.accept(this);
            if (ans != null)
                return ans;
        }
        return x.sub.accept(this);
    }

    /**
     * Visits an ExprUnary node (OP X) by calling accept() on X.
     */
    @Override
    public T visit(ExprUnary x) throws Err {
        return x.sub.accept(this);
    }

    /**
     * Visits a ExprVar node (this default implementation simply returns null)
     */
    @Override
    public T visit(ExprVar x) throws Err {
        return null;
    }

    /**
     * Visits a Sig node (this default implementation simply returns null)
     */
    @Override
    public T visit(Sig x) throws Err {
        return null;
    }

    /**
     * Visits a Field node (this default implementation simply returns null)
     */
    @Override
    public T visit(Field x) throws Err {
        return null;
    }
}
