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

public class SMTProgram
{
    private final List<Expression>             exprs                = new ArrayList<>();
    private final List<FunctionDeclaration>    functionDeclarations = new ArrayList<>();
    private final List<ConstantDeclaration>    constantDeclarations = new ArrayList<>();
    private final List<FunctionDefinition>     fcnDefs              = new ArrayList<>();
    private final List<Assertion>              assertions           = new ArrayList<>();
    private final List<Sort>                   sorts                = new ArrayList<>();

    public void addFunctionDeclaration(FunctionDeclaration declaration)
    {
        if(declaration != null)
        {
            this.functionDeclarations.add(declaration);
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
            this.functionDeclarations.add(fcn);
        }
    }
    
    public void addSort(Sort sort) 
    {
        if(sort != null) 
        {
            this.sorts.add(sort);
        }
    }    
    
    public void addFcnDef(FunctionDefinition fcnDef) 
    {
        if(fcnDef != null) 
        {
            this.fcnDefs.add(fcnDef);
        }
    }

    public void addConstantDeclaration(ConstantDeclaration constantDeclaration)
    {
        if(constantDeclaration != null)
        {
            this.constantDeclarations.add(constantDeclaration);
        }
    }

    public void addAssertion(Assertion assertion)
    {
        if(assertion != null)
        {
            this.assertions.add(assertion);
        }
    }
    
    public List<Sort> getSorts()
    {
        return this.sorts;
    }

    public List<FunctionDeclaration> getFunctionDeclarations()
    {
        return this.functionDeclarations;
    }

    public List<ConstantDeclaration> getConstantDeclarations()
    {
        return this.constantDeclarations;
    }
    
    public List<Expression> getExpressions() {
        return this.exprs;
    }
    
    public List<FunctionDefinition> getFunctionDefinition() {
        return this.fcnDefs;
    }

    public List<Assertion> getAssertions()
    {
        return this.assertions;
    }


}
