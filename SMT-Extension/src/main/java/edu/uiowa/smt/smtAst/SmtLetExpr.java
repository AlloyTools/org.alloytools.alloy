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

public class SmtLetExpr extends SmtExpr
{
    private final SmtExpr expr;
    private final Map<VariableDeclaration, SmtExpr> letVariables;

    public SmtLetExpr(Map<VariableDeclaration, SmtExpr> letVars, SmtExpr expr)
    {
        this.letVariables = new HashMap<>();
        this.expr = expr;
        for (Map.Entry<VariableDeclaration, SmtExpr> var : letVars.entrySet())
        {
            this.letVariables.put(var.getKey(), var.getValue());
        }
       checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        // make sure the types of the declared variables match their corresponding expressions

        for (Map.Entry<VariableDeclaration, SmtExpr> entry: letVariables.entrySet())
        {
            if(! entry.getKey().getSort().equals(entry.getValue().getSort()))
            {
                throw new RuntimeException(String.format("The variable '%1$s' has sort '%2$s' which is the different than '%3$s', the sort of its expression", entry.getKey().getName(), entry.getKey().getSort(), entry.getValue().getSort()));
            }
        }

        // check there is no typing error within the body
        expr.checkTypes();
    }

    public Map<VariableDeclaration, SmtExpr> getLetVariables()
    {
        return this.letVariables;
    }

    public SmtExpr getExpression()
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
    public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
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
        for (Map.Entry<VariableDeclaration, SmtExpr> entry: letVariables.entrySet())
        {
            freeVariables.remove(entry.getKey().getVariable());
        }
        return freeVariables;
    }

    @Override
    public SmtExpr substitute(Variable oldVariable, Variable newVariable)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
    {
        throw new UnsupportedOperationException();
    }
}
