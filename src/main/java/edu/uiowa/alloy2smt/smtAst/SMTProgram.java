/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import java.util.ArrayList;
import java.util.List;

public class SMTProgram {
    public List<Expression>             exprs       = new ArrayList<>();    
    public List<FunctionDeclaration>    fcnDecls    = new ArrayList<>();

    public void addExpr(Expression expr) 
    {
        if(expr != null) 
        {
            this.exprs.add(expr);
        }        
    }
    
    public void addFcn(FunctionDeclaration fcn) 
    {
        if(fcn != null) 
        {
            this.fcnDecls.add(fcn);
        }
    }    
}
