/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

public class BinaryExpression extends Expression
{
    private final Op            op;
    private final Expression    lhsExpr;
    private final Expression    rhsExpr;
    
    public BinaryExpression(Expression lhsExpr, Op op, Expression rhsExpr) 
    {
        this.op         = op;
        this.lhsExpr    = lhsExpr;
        this.rhsExpr    = rhsExpr;
    }
    
    public Expression getLhsExpr() 
    {
        return this.lhsExpr;
    }
    
    public Expression getRhsExpr() 
    {
        return this.rhsExpr;
    }    
    
    public Op getOp()
    {
        return this.op;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
    
    @Override
    public String toString()
    {
        String leftExprStr = this.lhsExpr.toString();
        String rhsExprStr = this.rhsExpr.toString();
        return leftExprStr + " " + this.op.toString() + " " + rhsExprStr;
    }
    
    public enum Op 
    {        
        OR ("or"),
        AND ("and"),  
        IMPLIES ("=>"),        
        PLUS ("+"),
        MINUS ("-"),
        MULTIPLY ("*"),
        DIVIDE ("/"),
        EQ ("="),
        NEQ ("<>"), //ToDo: clean this up
        GTE (">="),
        LTE ("<="),
        GT (">"),
        LT ("<"),        
        UNION ("union"),
        INTERSECTION ("intersection"),
        SETMINUS ("setminus"),        
        MEMBER ("member"),
        SUBSET ("subset"),
        JOIN ("join"),
        PRODUCT ("product"),
        TUPSEL ("tupSel");    

        private final String opStr;

        private Op(String op) 
        {
            this.opStr = op;
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }        
    }    
}
