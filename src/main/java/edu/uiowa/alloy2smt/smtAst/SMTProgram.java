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
    private final List<Expression>             exprs       = new ArrayList<>();    
    private final List<VariableDeclaration>    varDecls    = new ArrayList<>();
    private final List<FunctionDeclaration>    fcnDecls    = new ArrayList<>();
    private final List<FunctionDefinition>     fcnDefs     = new ArrayList<>();    

    public void addVarDecl(VariableDeclaration varDecl) 
    {
        if(varDecl != null) 
        {
            this.varDecls.add(varDecl);
        }        
    }    
    
    public void addExpr(Expression expr) 
    {
        if(expr != null) 
        {
            this.exprs.add(expr);
        }        
    }
    
    public void addFcnDecl(FunctionDeclaration fcn) 
    {
        if(fcn != null) 
        {
            this.fcnDecls.add(fcn);
        }
    } 
    
    public void addFcnDef(FunctionDefinition fcnDef) 
    {
        if(fcnDef != null) 
        {
            this.fcnDefs.add(fcnDef);
        }
    }     

    public List<VariableDeclaration> getVariableDecls() {
        return this.varDecls;
    }
    
    public List<Expression> getExpressions() {
        return this.exprs;
    }
    
    public List<FunctionDeclaration> getFunctionDeclaration() {
        return this.fcnDecls;
    } 
    
    public List<FunctionDefinition> getFunctionDefinition() {
        return this.fcnDefs;
    }     
}
