/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
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
            constantExpression = new ConstantExpression(this);
        }
        else
        {
            constantExpression = null;
        }
    }

    public FunctionDeclaration(String name, Sort inputSort, Sort outputSort)
    {
        super(name, outputSort);
        this.inputSorts = Arrays.asList(inputSort);

        if(this.inputSorts.isEmpty())
        {
            constantExpression = new ConstantExpression(this);
        }
        else
        {
            constantExpression = null;
        }
    }

    public FunctionDeclaration(String name, Sort outputSort)
    {
        super(name, outputSort);
        this.inputSorts         = new ArrayList<>();
        this.constantExpression = new ConstantExpression(this);
    } 
    
    public FunctionDeclaration(String name, Sort outputSort, Sort ... inputSorts)
    {
        super(name, outputSort);
        this.inputSorts = Arrays.asList(inputSorts);

        if(this.inputSorts.isEmpty())
        {
            constantExpression = new ConstantExpression(this);
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

    @Override
    public ConstantExpression getConstantExpr()
    {
        if(this.constantExpression != null)
        {
            return this.constantExpression;
        }
        // this is a function call
        throw new UnsupportedOperationException();
    }

    public FunctionCallExpression getCallExpr(Expression ... expressions)
    {
        return new FunctionCallExpression(this.getName(), expressions);
    }


    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
