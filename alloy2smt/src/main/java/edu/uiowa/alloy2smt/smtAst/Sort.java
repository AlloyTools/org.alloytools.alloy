/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import edu.uiowa.alloy2smt.printers.SmtLibPrettyPrinter;

public class Sort extends Expression
{
    private final String name;
    private final int    arity;

    public Sort(String name, int arity)
    {
        this.name   = name;
        this.arity  = arity;
    }

    public String getName()
    {
        return this.name;
    }

    @Override
    public String toString()
    {
        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
        printer.visit(this);
        return printer.getSmtLib();
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return this;
    }
}
