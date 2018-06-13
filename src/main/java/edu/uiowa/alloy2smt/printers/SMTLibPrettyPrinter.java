/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.SMTAst;

public class SMTLibPrettyPrinter
{
    private final SMTAst root;

    public SMTLibPrettyPrinter(SMTAst root)
    {
        this.root = root;
    }

    public String print()
    {
        throw new UnsupportedOperationException();
    }
}
