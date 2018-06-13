/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.SMTProgram;

public class SMTLibPrettyPrinter
{
    private final SMTProgram program;

    public SMTLibPrettyPrinter(SMTProgram program)
    {
        this.program = program;
    }

    public String print()
    {
        throw new UnsupportedOperationException();
    }
}
