/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class QuantifiedExpression extends Expression
{
    private final Expression                  expr;
    private final List<BoundVariableDeclaration>   boundVars;
    private final Op                          op;
    
    public QuantifiedExpression(Op op, List<BoundVariableDeclaration> boundVars, Expression expr)
    {
        this.boundVars  = new ArrayList<>();        
        this.expr       = expr;
        this.op         = op;
        for(BoundVariableDeclaration bdVar : boundVars)
        {
            this.boundVars.add(bdVar);
        }
    }
    
    public QuantifiedExpression(Op op, Expression expr, BoundVariableDeclaration... boundVars)
    {
        this.boundVars  = Arrays.asList(boundVars);
        this.expr       = expr;
        this.op         = op;
    }
    
    public List<BoundVariableDeclaration> getBoundVars()
    {
        return this.boundVars;
    }
    
    public Expression getExpression()
    {
        return this.expr;
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
        FORALL ("forall"),
        EXISTS ("exists"),
        LET ("let");    

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
