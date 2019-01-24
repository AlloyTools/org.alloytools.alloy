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

    public enum Op 
    {        
        OR ("or"),
        AND ("and"),  
        IMPLIES ("=>"),        
        PLUS ("+"),
        MINUS ("-"),
        MULTIPLY ("*"),
        DIVIDE ("/"),
        MOD ("mod"),
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

        Op(String op)
        {
            this.opStr = op;
        }

        public static Op getOp(String operator)
        {
            switch (operator)
            {
                case"or"            : return OR;
                case "and"          : return AND;
                case "=>"           : return IMPLIES;
                case "+"            : return PLUS;
                case "-"            : return MINUS;
                case "*"            : return MULTIPLY;
                case "/"            : return DIVIDE;
                case "mod"          : return MOD;
                case "="            : return EQ;
                case ">="           : return GTE;
                case "<="           : return LTE;
                case ">"            : return GT;
                case "<"            : return LT;
                case "union"        : return UNION;
                case "intersection" : return INTERSECTION;
                case "setminus"     : return SETMINUS;
                case "member"       : return MEMBER;
                case "subset"       : return SUBSET;
                case "join"         : return JOIN;
                case "product"      : return PRODUCT;
                case "tupSel"       : return TUPSEL;
                default:
                    throw new UnsupportedOperationException("Operator " + operator + " is not defined");
            }
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }        
    }    
}
