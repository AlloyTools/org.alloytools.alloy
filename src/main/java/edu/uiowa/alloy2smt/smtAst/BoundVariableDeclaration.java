/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class BoundVariableDeclaration extends SMTAst
{
    private final String                    name;
    private final Sort                      sort;
    private final ConstantExpression        constantExpression;

    public BoundVariableDeclaration(String name, Sort sort)
    {
        this.name = name;
        this.sort = sort;
        this.constantExpression = new ConstantExpression(this.name);
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

    @Override
    public void accept(SMTAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
