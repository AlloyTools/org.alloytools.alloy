/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class FunctionDefinition extends SMTAst
{
    public final String funcName;
    public final List<BoundVariableDeclaration>   inputVarDecls;
    public final Sort         outputSort;
    public final Expression   expression;
    
    public FunctionDefinition(String funcName, List<BoundVariableDeclaration> inputSort, Sort outputSort, Expression expression) 
    {
        this.funcName = funcName;
        this.inputVarDecls = inputSort;
        this.outputSort = outputSort;
        this.expression = expression;
    }
    
    public FunctionDefinition(String funcName, BoundVariableDeclaration inputSort, Sort outputSort, Expression expression) 
    {
        this.funcName = funcName;
        this.inputVarDecls = Arrays.asList(inputSort);
        this.outputSort = outputSort;
        this.expression = expression;
    }

    public FunctionDefinition(String funcName, Sort outputSort, Expression expression) 
    {
        this.funcName = funcName;
        this.inputVarDecls = new ArrayList<>();
        this.outputSort = outputSort;
        this.expression = expression;
    }  
    
    public FunctionDefinition(String funcName, Sort outputSort, Expression expression, BoundVariableDeclaration ... inputSorts) 
    {
        this.funcName = funcName;
        this.inputVarDecls = Arrays.asList(inputSorts);
        this.outputSort = outputSort;
        this.expression = expression;
    }      
    
    public List<BoundVariableDeclaration> getInputSorts()
    {
        return this.inputVarDecls;
    }
    
    public Sort getOutputSort()
    {
        return this.outputSort;
    }
    
    public Expression getExpression()
    {
        return this.expression;
    }
    
    public String getFuncName()
    {
        return this.funcName;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}