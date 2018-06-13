/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class VariableDeclaration {
    private final String    varName;
    private final Sort      varSort;
    
    public VariableDeclaration(String varName, Sort varSort) 
    {
        this.varName = varName;
        this.varSort = varSort;
    }
}
