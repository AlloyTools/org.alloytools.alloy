/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class Assertion extends SmtAst
{
    private final Expression  expression;

    private final String comment;

    private final String symbolicName;

    public Assertion(String symbolicName, String comment, Expression expression)
    {
        this.symbolicName = symbolicName;
        this.comment = comment;
        this.expression = expression;
    }

    public String getComment()
    {
        return this.comment;
    }

    public Expression getExpression()
    {
        return this.expression;
    }

    public String getSymbolicName()
    {
        return symbolicName;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
