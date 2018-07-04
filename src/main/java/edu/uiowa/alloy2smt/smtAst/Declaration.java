/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

abstract public class Declaration extends SMTAst
{
    private final String                name;
    private final Sort                  sort;

    protected ConstantExpression    constantExpression;

    protected Declaration(String name, Sort sort)
    {
        this.name = name;
        this.sort = sort;
        this.constantExpression = new ConstantExpression(this);
    }

    public String getName()
    {
        return this.name;
    }

    public Sort getSort()
    {
        return this.sort;
    }

    public ConstantExpression getConstantExpr()
    {
        return this.constantExpression;
    }
}
