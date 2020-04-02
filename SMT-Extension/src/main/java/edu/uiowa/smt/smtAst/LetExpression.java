/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class LetExpression extends Expression
{
    private final Expression expr;
    private final Map<VariableDeclaration, Expression> letVariables;

    public LetExpression(Map<VariableDeclaration, Expression> letVars, Expression expr)
    {
        this.letVariables = new HashMap<>();
        this.expr = expr;
        for (Map.Entry<VariableDeclaration, Expression> var : letVars.entrySet())
        {
            this.letVariables.put(var.getKey(), var.getValue());
        }
       checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        // make sure the types of the declared variables match their corresponding expressions

        for (Map.Entry<VariableDeclaration, Expression> entry: letVariables.entrySet())
        {
            if(! entry.getKey().getSort().equals(entry.getValue().getSort()))
            {
                throw new RuntimeException(String.format("The variable '%1$s' has sort '%2$s' which is the different than '%3$s', the sort of its expression", entry.getKey().getName(), entry.getKey().getSort(), entry.getValue().getSort()));
            }
        }

        // check there is no typing error within the body
        expr.checkTypes();
    }

    public Map<VariableDeclaration, Expression> getLetVariables()
    {
        return this.letVariables;
    }

    public Expression getExpression()
    {
        return this.expr;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return expr.getSort();
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Variable> getFreeVariables()
    {
        List<Variable> freeVariables = expr.getFreeVariables();
        for (Map.Entry<VariableDeclaration, Expression> entry: letVariables.entrySet())
        {
            freeVariables.remove(entry.getKey().getVariable());
        }
        return freeVariables;
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        throw new UnsupportedOperationException();
    }
}
