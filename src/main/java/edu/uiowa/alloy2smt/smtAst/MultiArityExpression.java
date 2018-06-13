/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import java.util.Arrays;
import java.util.List;

public class MultiArityExpression 
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
    
    public enum Op 
    {        
        MKTUPLE ("mkTuple"),
        INSERT ("insert");    

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
