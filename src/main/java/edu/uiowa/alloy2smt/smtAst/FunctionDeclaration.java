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

public class FunctionDeclaration extends SMTAst
{
    private final List<Sort>   inputSorts;
    private final Sort         outputSort;
    
    public FunctionDeclaration(List<Sort> inputSort, Sort outputSort) 
    {
        this.inputSorts = inputSort;
        this.outputSort = outputSort;
    }
    
    public FunctionDeclaration(Sort inputSort, Sort outputSort) 
    {
        this.inputSorts = Arrays.asList(inputSort);
        this.outputSort = outputSort;
    }

    public FunctionDeclaration(Sort outputSort) 
    {
        this.inputSorts = new ArrayList<>();
        this.outputSort = outputSort;
    } 
    
    public FunctionDeclaration(Sort outputSort, Sort ... inputSorts) 
    {
        this.inputSorts = Arrays.asList(inputSorts);
        this.outputSort = outputSort;
    }     
    
    public List<Sort> getInputSorts()
    {
        return this.inputSorts;
    }
    
    public Sort getOutputSort()
    {
        return this.outputSort;
    }   

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
