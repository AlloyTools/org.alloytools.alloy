/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtLibPrettyPrinter;

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
}
