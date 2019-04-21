/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtLibPrettyPrinter;

import java.util.Map;

public abstract class Expression extends SmtAst
{
    @Override
    public String toString()
    {
        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
        printer.visit(this);
        return printer.getSmtLib();
    }

    public abstract Sort getSort();
    protected void checkTypes(){}

    public abstract Expression evaluate(Map<String, FunctionDefinition> functions);

    @Override
    public abstract boolean equals(Object object);
}
