/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class ConstantDefinition extends FunctionDefinition
{
    public ConstantDefinition(String name,  Sort outputSort, Expression expression)
    {
        super(name, outputSort, expression);
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}