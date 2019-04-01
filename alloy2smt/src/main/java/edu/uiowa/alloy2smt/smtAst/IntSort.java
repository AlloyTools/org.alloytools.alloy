/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

public class IntSort extends Sort
{
    private static IntSort instance = new IntSort();

    private IntSort()
    {
        super("Int", 0);
    }

    public static IntSort getInstance()
    {
        return instance;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
}
