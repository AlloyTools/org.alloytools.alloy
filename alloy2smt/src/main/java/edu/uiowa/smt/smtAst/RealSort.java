/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class RealSort extends Sort
{
    public RealSort()
    {
        super("Real", 0);
    }
    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof RealSort))
        {
            return false;
        }
        return true;
    }
}
