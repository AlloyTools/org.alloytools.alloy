/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class IntSort extends Sort
{
    private final String intSort = "Int";
    
    public String getSortName()
    {
        return this.intSort;
    }
    
    @Override
    public String toString() 
    {
        return this.intSort;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
