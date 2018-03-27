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
 * This abstract class defines what a Return Visitor's interface needs to be.
 */

public abstract class VisitReturn<T> {

    /** Constructs a VisitReturn object. */
    public VisitReturn() {}

    /**
     * This is the start method that begins a traversal over the given expression.
     */
    public final T visitThis(Expr x) throws Err {
        return x.accept(this);
    }

    /** Visits a ExprBad node */
    public T visit(ExprBad x) throws Err {
        throw x.errors.pick();
    }

    /** Visits a ExprBadCall node */
    public T visit(ExprBadCall x) throws Err {
        throw x.errors.pick();
    }

    /** Visits a ExprBadJoin node */
    public T visit(ExprBadJoin x) throws Err {
        throw x.errors.pick();
    }

    /** Visits an ExprBinary node. */
    public abstract T visit(ExprBinary x) throws Err;

    /** Visits an ExprList node. */
    public abstract T visit(ExprList x) throws Err;

    /** Visits an ExprCall node. */
    public abstract T visit(ExprCall x) throws Err;

    /** Visits an ExprConstant node. */
    public abstract T visit(ExprConstant x) throws Err;

    /** Visits an ExprITE node. */
    public abstract T visit(ExprITE x) throws Err;

    /** Visits an ExprLet node. */
    public abstract T visit(ExprLet x) throws Err;

    /** Visits an ExprQt node. */
    public abstract T visit(ExprQt x) throws Err;

    /** Visits an ExprUnary node. */
    public abstract T visit(ExprUnary x) throws Err;

    /** Visits an ExprVar node. */
    public abstract T visit(ExprVar x) throws Err;

    /** Visits a Sig node. */
    public abstract T visit(Sig x) throws Err;

    /** Visits a Field node. */
    public abstract T visit(Field x) throws Err;
}
