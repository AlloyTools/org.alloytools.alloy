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
    private final String                name;
    private final List<Sort>            inputSorts;
    private final Sort                  outputSort;
    private final ConstantExpression    constantExpression;

    
    public FunctionDeclaration(String name, List<Sort> inputSort, Sort outputSort)
    {
        this.name       = name;
        this.inputSorts = inputSort;
        this.outputSort = outputSort;

        if(this.inputSorts.isEmpty())
        {
            constantExpression = new ConstantExpression(name);
        }
        else
        {
            constantExpression = null;
        }
    }
    
    public FunctionDeclaration(String name, Sort inputSort, Sort outputSort)
    {
        this.name       = name;
        this.inputSorts = Arrays.asList(inputSort);
        this.outputSort = outputSort;

        if(this.inputSorts.isEmpty())
        {
            constantExpression = new ConstantExpression(name);
        }
        else
        {
            constantExpression = null;
        }
    }

    public FunctionDeclaration(String name, Sort outputSort)
    {
        this.name               = name;
        this.inputSorts         = new ArrayList<>();
        this.outputSort         = outputSort;
        this.constantExpression = new ConstantExpression(name);
    } 
    
    public FunctionDeclaration(String name, Sort outputSort, Sort ... inputSorts)
    {
        this.name       = name;
        this.inputSorts = Arrays.asList(inputSorts);
        this.outputSort = outputSort;

        if(this.inputSorts.isEmpty())
        {
            constantExpression = new ConstantExpression(name);
        }
        else
        {
            constantExpression = null;
        }
    }     
    
    public List<Sort> getInputSorts()
    {
        return this.inputSorts;
    }

    public String getName()
    {
        return this.name;
    }

    public ConstantExpression getConstantExpr()
    {
        return this.constantExpression;
    }

    public FunctionCallExpression getCallExpr(Expression ... expressions)
    {
        return new FunctionCallExpression(this.name, expressions);
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
