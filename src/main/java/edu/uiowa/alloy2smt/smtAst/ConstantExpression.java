/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class ConstantExpression extends Expression
{
    private final String varName;
    
    public ConstantExpression(String varName)
    {
        this.varName = varName;
    }
    
    public String getVarName()
    {
        return this.varName;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
