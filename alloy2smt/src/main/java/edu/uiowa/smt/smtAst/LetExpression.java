/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.HashMap;
import java.util.Map;

public class LetExpression extends Expression
{
    private final Expression expr;
    private final Map<String, Expression> letVariables;

    public LetExpression(Map<String, Expression> letVars, Expression expr)
    {
        this.letVariables = new HashMap<>();
        this.expr = expr;
        for (Map.Entry<String, Expression> var : letVars.entrySet())
        {
            this.letVariables.put(var.getKey(), var.getValue());
        }
    }


    public Map<String, Expression> getLetVariables()
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
