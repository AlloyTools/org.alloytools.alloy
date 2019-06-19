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
    private final String name; // sanitized name for cvc4
    private String originalName; // the original name of the declaration
    private final Sort sort;

    protected Variable variable;

    protected Declaration(String name, Sort sort)
    {
        this.name = name;
        this.sort = sort;
        this.variable = new Variable(this);
        this.originalName = name; // by default, name and original name are the same
    }

    public String getName()
    {
        return this.name;
    }

    public void setOriginalName(String originalName)
    {
        this.originalName = originalName;
    }

    public String getOriginalName()
    {
        return originalName;
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
