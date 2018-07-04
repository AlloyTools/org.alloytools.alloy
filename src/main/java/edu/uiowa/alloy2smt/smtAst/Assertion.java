/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class Assertion
{
    private final Expression  expression;

    private final String      name;

    public Assertion(Expression expression)
    {
        this.name       = "";
        this.expression = expression;
    }

    public Assertion(String name, Expression expression)
    {
        this.name       = name;
        this.expression = expression;
    }

    public String getName()
    {
        return this.name;
    }

    public Expression getExpression()
    {
        return this.expression;
    }
}
