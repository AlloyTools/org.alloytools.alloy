/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

public class UninterpretedSort extends Sort
{
    public UninterpretedSort(String sortName) 
    {
        super(sortName, 0);
    }
    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
    @Override
    public boolean equals(Object object)
    {
        if (object == this)
        {
            return true;
        }

        if (!(object instanceof UninterpretedSort))
        {
            return false;
        }

        UninterpretedSort sort = (UninterpretedSort) object;
        return sort.getName().equals(this.getName());
    }
}
