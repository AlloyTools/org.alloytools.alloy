/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class RealSort extends Sort
{
    private final String realSort = "real";
    
    public String getSortName()
    {
        return this.realSort;
    }
    
    @Override
    public String toString() 
    {
        return this.realSort;
    }    

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
