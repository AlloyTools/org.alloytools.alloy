/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class FunctionDeclaration extends Declaration
{
    private final List<Sort>            inputSorts;

    public FunctionDeclaration(String name, List<Sort> inputSort, Sort outputSort)
    {
        super(name, outputSort);

        this.inputSorts = inputSort;

        if(this.inputSorts.isEmpty())
        {
            variable = new Variable(this);
        }
        else
        {
            variable = null;
        }
    }

    public FunctionDeclaration(String name, Sort inputSort, Sort outputSort)
    {
        super(name, outputSort);
        this.inputSorts = Arrays.asList(inputSort);

        if(this.inputSorts.isEmpty())
        {
            variable = new Variable(this);
        }
        else
        {
            variable = null;
        }
    }

    public FunctionDeclaration(String name, Sort outputSort)
    {
        super(name, outputSort);
        this.inputSorts         = new ArrayList<>();
        this.variable = new Variable(this);
    } 
    
    public FunctionDeclaration(String name, Sort outputSort, Sort ... inputSorts)
    {
        super(name, outputSort);
        this.inputSorts = Arrays.asList(inputSorts);

        if(this.inputSorts.isEmpty())
        {
            variable = new Variable(this);
        }
        else
        {
            variable = null;
        }
    }     
    
    public List<Sort> getInputSorts()
    {
        return this.inputSorts;
    }

    @Override
    public Variable getVariable()
    {
        if(this.variable != null)
        {
            return this.variable;
        }
        // this is a function call
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
