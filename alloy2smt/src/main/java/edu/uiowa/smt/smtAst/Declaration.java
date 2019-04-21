/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

abstract public class Declaration extends SmtAst
{
    private final String                name;
    private final Sort                  sort;

    protected Variable variable;

    protected Declaration(String name, Sort sort)
    {
        this.name = name;
        this.sort = sort;
        this.variable = new Variable(this);
    }

    public String getName()
    {
        return this.name;
    }

    public Sort getSort()
    {
        return this.sort;
    }

    public Variable getVariable()
    {
        return this.variable;
    }
}
