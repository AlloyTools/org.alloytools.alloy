/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class VariableDeclaration extends Declaration
{
    private Expression constraint;

    public VariableDeclaration(String name, Sort sort, Expression constraint)
    {
        super(name, sort);
    }

    public void setConstraint(Expression constraint)
    {
        this.constraint = constraint;
    }

    public Expression getConstraint()
    {
        return constraint;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
