/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class BinaryExpression extends Expression
{
    private final Expression lhsExpr;
    private final Expression rhsExpr;
    
    public BinaryExpression(Expression lhsExpr, Expression rhsExpr) 
    {
        this.lhsExpr = lhsExpr;
        this.rhsExpr = rhsExpr;
    }
    
    public Expression getLhsExpr() 
    {
        return this.lhsExpr;
    }
    
    public Expression getRhsExpr() 
    {
        return this.rhsExpr;
    }    

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
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
        NEQ ("<>"),
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
        PRODUCT ("product");    

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
