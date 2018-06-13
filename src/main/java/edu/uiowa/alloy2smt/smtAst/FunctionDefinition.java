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
    public List<Sort>   inputSort;
    public Sort         outputSort;
    public Expression   expression;
    
    public FunctionDefinition(List<Sort> inputSort, Sort outputSort, Expression expression) 
    {
        this.inputSort  = inputSort;
        this.outputSort = outputSort;
        this.expression = expression;
    }
    
    public FunctionDefinition(Sort inputSort, Sort outputSort, Expression expression) 
    {
        this.inputSort  = Arrays.asList(inputSort);
        this.outputSort = outputSort;
        this.expression = expression;
    }

    public FunctionDefinition(Sort outputSort, Expression expression) 
    {
        this.inputSort  = new ArrayList<>();
        this.outputSort = outputSort;
        this.expression = expression;
    }    
}