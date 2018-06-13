/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class StringSort extends Sort
{
    private final String stringSort = "string";
    
    public String getSortName()
    {
        return this.stringSort;
    }
    
    @Override
    public String toString() 
    {
        return this.stringSort;
    }      

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
