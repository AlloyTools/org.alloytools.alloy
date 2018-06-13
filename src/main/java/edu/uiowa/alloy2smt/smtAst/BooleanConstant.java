/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class BooleanConstant 
{
    private final boolean value;
    
    public BooleanConstant(boolean value)
    {
        this.value = value;
    }
    
    public boolean getBooleanConstValue()
    {
        return this.value;
    }
}
