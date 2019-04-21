/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smt.smtAst;

import edu.uiowa.alloy2smt.smt.printers.SmtAstVisitor;

public class VariableDeclaration extends Declaration
{
    public VariableDeclaration(String name, Sort sort)
    {
        super(name, sort);
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
