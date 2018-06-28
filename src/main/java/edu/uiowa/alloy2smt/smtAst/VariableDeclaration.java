/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class VariableDeclaration extends SMTAst 
{
    private final String                varName;
    private final Sort                  varSort;
    private final VariableExpression    variableExpression;
    
    public VariableDeclaration(String varName, Sort varSort) 
    {
        this.varName = varName;
        this.varSort = varSort;
        variableExpression = new VariableExpression(varName);
    }
    
    public String getVarName()
    {
        return this.varName;
    }
    
    public Sort getVarSort()
    {
        return this.varSort;
    }

    public VariableExpression getVarExpr()
    {
        return this.variableExpression;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
