/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class FunctionDefinition
{
    private final List<Sort>   inputSorts;
    private final Sort         outputSort;
    private final Expression   expression;
    
    public FunctionDefinition(List<Sort> inputSort, Sort outputSort, Expression expression) 
    {
        this.inputSorts = inputSort;
        this.outputSort = outputSort;
        this.expression = expression;
    }
    
    public FunctionDefinition(Sort inputSort, Sort outputSort, Expression expression) 
    {
        this.inputSorts = Arrays.asList(inputSort);
        this.outputSort = outputSort;
        this.expression = expression;
    }

    public FunctionDefinition(Sort outputSort, Expression expression) 
    {
        this.inputSorts = new ArrayList<>();
        this.outputSort = outputSort;
        this.expression = expression;
    }  
    
    public FunctionDefinition(Sort outputSort, Expression expression, Sort ... inputSorts) 
    {
        this.inputSorts = Arrays.asList(inputSorts);
        this.outputSort = outputSort;
        this.expression = expression;
    }      
    
    public List<Sort> getInputSorts()
    {
        return this.inputSorts;
    }
    
    public Sort getOutputSort()
    {
        return this.outputSort;
    }
    
    public Expression getExpression()
    {
        return this.expression;
    }
}