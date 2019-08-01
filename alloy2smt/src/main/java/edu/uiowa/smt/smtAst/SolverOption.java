/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class SolverOption extends SmtAst
{
    public String name;
    public String value;

    public SolverOption(String name, String value)
    {
        this.name   = name;
        this.value  = value;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
