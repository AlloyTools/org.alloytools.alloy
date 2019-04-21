/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class QuantifiedExpression extends Expression
{
    private final Expression                  expr;
    private final List<VariableDeclaration>   boundVars;
    private final Op                          op;
    
    public QuantifiedExpression(Op op, List<VariableDeclaration> boundVars, Expression expr)
    {
        this.boundVars  = new ArrayList<>();        
        this.expr       = expr;
        this.op         = op;
        for(VariableDeclaration bdVar : boundVars)
        {
            this.boundVars.add(bdVar);
        }
        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        if(expr.getSort() != AbstractTranslator.boolSort)
        {
            throw new RuntimeException(String.format("The sort '%1$s' of the quantified expression is not boolean", expr.getSort()));
        }
    }

    public QuantifiedExpression(Op op, Expression expr, VariableDeclaration... boundVars)
    {
        this.boundVars  = Arrays.asList(boundVars);
        this.expr       = expr;
        this.op         = op;
    }
    
    public List<VariableDeclaration> getBoundVars()
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

    @Override
    public Sort getSort()
    {
        return AbstractTranslator.boolSort;
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof QuantifiedExpression))
        {
            return false;
        }
        QuantifiedExpression quantifiedObject = (QuantifiedExpression) object;
        if(! boundVars.equals(quantifiedObject.boundVars))
        {
            return false;
        }
        return op ==  quantifiedObject.op &&
                expr.equals(quantifiedObject.expr);
    }
}
