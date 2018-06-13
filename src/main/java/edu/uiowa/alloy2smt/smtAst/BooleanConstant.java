/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class BooleanConstant extends SMTAst
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

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
