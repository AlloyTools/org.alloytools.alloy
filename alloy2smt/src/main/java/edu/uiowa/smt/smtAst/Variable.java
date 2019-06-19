/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.Map;

public class Variable extends Expression
{
    private final Declaration declaration;

    Variable(Declaration declaration)
    {
        this.declaration = declaration;
    }
    
    public String getName()
    {
        return this.declaration.getName();
    }

    public Declaration getDeclaration()
    {
        return this.declaration;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return declaration.getSort();
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
        if(!(object instanceof Variable))
        {
            return false;
        }
        Variable constantObject = (Variable) object;
        return declaration.equals(constantObject.declaration);
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        if(this.equals(newVariable))
        {
            throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
        }
        if(this.equals(oldVariable))
        {
            return newVariable;
        }
        return  this;
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        if(oldExpression.equals(this))
        {
            return newExpression;
        }
        return  this;
    }
}
