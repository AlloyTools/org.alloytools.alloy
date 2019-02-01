/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;

import java.util.ArrayList;
import java.util.List;

public class UnaryExpression extends Expression
{    
    private final Op op;
    private final Expression expr;
    private final List<Expression> exprs;
    
    public UnaryExpression(Op op, Expression expr)
    {
        this.op     = op;
        this.expr   = expr;
        this.exprs  = null;
    }
    
    public UnaryExpression(Op op, List<Expression> exprs)
    {
        this.op     = op;
        this.expr   = null;
        this.exprs  = new ArrayList<>();
        for(Expression e : exprs)
        {
            this.exprs.add(e);
        }
        
    }  
    
    public UnaryExpression(Op op, Expression ... exprs)
    {
        this.op     = op;
        this.expr   = null;
        this.exprs  = new ArrayList<>();
        for(Expression e : exprs)
        {
            this.exprs.add(e);
        }
        
    }      

    public Op getOP() 
    {
        return this.op;
    }
    
    public Expression getExpression() 
    {
        return this.expr;
    }
    
    public List<Expression> getExpressions() 
    {
        return this.exprs;
    }   
    
    @Override
    public String toString()
    {
        String exprStr = "";
        
        if(this.expr != null)
        {
            exprStr = this.expr.toString();
        }
        if(this.exprs != null)
        {
            for(Expression e : this.exprs)
            {
                exprStr += e.toString() + " ";
            }
        }
        
        return this.op.toString() + " " + exprStr;
    }    
    
    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
    
    public enum Op 
    {	        
        NOT ("not"),
        DISTINCT ("distinct"), //ToDo: clean up this
        COMPLEMENT ("complement"),
        TRANSPOSE ("transpose"),
        TCLOSURE("tclosure"),
        SINGLETON("singleton"),
        UNIVSET("as univset"),
        EMPTYSET("as emptyset");

        private final String opStr;

        Op(String str)
        {
            this.opStr = str;
        }

        public static Op getOp(String operator)
        {
            switch (operator)
            {
                case"not"           : return NOT;
                case "distinct"     : return DISTINCT;
                case "complement"   : return COMPLEMENT;
                case "transpose"    : return TRANSPOSE;
                case "tclosure"     : return TCLOSURE;
                case "singleton"    : return SINGLETON;
                case "as univset"   : return UNIVSET;
                case "as emptyset"  : return EMPTYSET;
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

    @Override
    public Sort getSort() throws Exception
    {
        switch (op)
        {
            case NOT: return Alloy2SmtTranslator.boolSort;
            case DISTINCT: return Alloy2SmtTranslator.boolSort ;
            case IMPLIES: return Alloy2SmtTranslator.boolSort;
            case PLUS: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case MINUS: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
    }
}
