package edu.mit.csail.sdg.ast;

import java.util.IdentityHashMap;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Sig.Field;

/**
 * Acts like VisitQuery but never traverses a node more than once.
 *
 */
public class VisitQueryOnce<T> extends VisitQuery<T> {

    final IdentityHashMap<Expr,Object> visited = new IdentityHashMap<Expr,Object>();

    @Override
    public T visit(ExprBinary x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprList node F[X1,X2,X3..] by calling accept() on X1, X2, X3...
     */
    @Override
    public T visit(ExprList x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprCall node F[X1,X2,X3..] by calling accept() on X1, X2, X3...
     */
    @Override
    public T visit(ExprCall x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprConstant node (this default implementation simply returns null)
     */
    @Override
    public T visit(ExprConstant x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprITE node (C => X else Y) by calling accept() on C, X, then Y.
     */
    @Override
    public T visit(ExprITE x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprLet node (let a=x | y) by calling accept() on "a", "x", then
     * "y".
     */
    @Override
    public T visit(ExprLet x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprQt node (all a,b,c:X1, d,e,f:X2... | F) by calling accept() on
     * a,b,c,X1,d,e,f,X2... then on F.
     */
    @Override
    public T visit(ExprQt x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits an ExprUnary node (OP X) by calling accept() on X.
     */
    @Override
    public T visit(ExprUnary x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits a ExprVar node (this default implementation simply returns null)
     */
    @Override
    public T visit(ExprVar x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits a Sig node (this default implementation simply returns null)
     */
    @Override
    public T visit(Sig x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Visits a Field node (this default implementation simply returns null)
     */
    @Override
    public T visit(Field x) throws Err {
        if (visited(x))
            return null;
        else
            return super.visit(x);
    }

    /**
     * Will be called for all visit methods. If it returns true then null is
     * returned otherwise the normal visit method is called.
     *
     * @param x the expr that is being visited
     * @return true if this expr was already visited
     */
    protected boolean visited(Expr x) {
        return visited.put(x, x) != null;
    }

}
