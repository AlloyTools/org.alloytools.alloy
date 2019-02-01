/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

public class ConstantExpression extends Expression
{
    private final Declaration declaration;

    public ConstantExpression(Declaration declaration)
    {
        this.declaration = declaration;
    }
    
    public String getVarName()
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
    public Sort getSort() throws Exception
    {
        return declaration.getSort();
    }
}
