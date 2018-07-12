/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class UnaryExpression extends Expression
{    
    private final Op op;
    private final Expression expr;
    
    public UnaryExpression(Op op, Expression expr)
    {
        this.op     = op;
        this.expr   = expr;
    }
    
    public Op getOP() 
    {
        return this.op;
    }
    
    public Expression getExpression() 
    {
        return this.expr;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
    
    public enum Op 
    {	        
        NOT ("not"),
        COMPLEMENT ("complement"),
        TRANSPOSE ("transpose"),
        TCLOSURE("tclosure"),
        SINGLETON("singleton"),
        UNIVSET("as univset"),
        EMPTYSET("as emptyset");

        private final String opStr;

        private Op(String str) 
        {
            this.opStr = str;
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }    
    }     
}
