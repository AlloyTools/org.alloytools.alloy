/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

import java.util.Arrays;
import java.util.List;

public class MultiArityExpression extends Expression
{
    private final Op op;
    private final List<Expression> exprs;
    
    public MultiArityExpression(Op op, List<Expression> exprs)
    {
        this.op     = op;
        this.exprs  = exprs;
    }
    
    public MultiArityExpression(Op op, Expression ... exprs)
    {
        this.op     = op;
        this.exprs  = Arrays.asList(exprs);
    }    
    
    public Op getOp()
    {
        return this.op;
    }
    
    public List<Expression> getExpressions()
    {
        return this.exprs;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    public enum Op 
    {        
        MKTUPLE ("mkTuple"),
        INSERT ("insert"),
        DISTINCT ("distinct");
        //ToDo: add other operators like and, or, ...
        private final String opStr;

        Op(String op)
        {
            this.opStr = op;
        }

       public static Op getOp(String operator)
       {
           switch (operator)
           {
               case "mkTuple"   : return MKTUPLE;
               case "insert"    : return INSERT;
               case "distinct"  : return DISTINCT;
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
