/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

import java.util.Arrays;
import java.util.List;

public class FunctionCallExpression extends Expression
{
    private final FunctionDeclaration function;
    private final List<Expression>  arguments;

    public FunctionCallExpression(FunctionDeclaration function, Expression ... arguments)
    {
        this.function = function;
        this.arguments      = Arrays.asList(arguments);
        checkTypes();
    }
    
    public FunctionCallExpression(FunctionDeclaration function, List<Expression> arguments)
    {
        this.function = function;
        this.arguments      = arguments;
        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        if(function.getInputSorts().size() != arguments.size())
        {
            throw new RuntimeException(String.format("Function '%1$s' expects %2$d arguments but %3$d arguments were passed", function.getName(), function.getInputSorts().size(), arguments.size()));
        }

        for(int i = 0; i < arguments.size(); i++)
        {
            Sort actualSort = arguments.get(i).getSort();
            Sort expectedSort = function.getInputSorts().get(i);
            if (!actualSort.equals(expectedSort))
            {
                throw new RuntimeException(String.format("Function '%1$s' expects argument %2$d to have sort '%3$s', but it has sort '%4$s'", function.getName(), i,  expectedSort, actualSort));
            }
        }
    }

    public String getFunctionName()
    {
        return this.function.getName();
    }

    public List<Expression>  getArguments()
    {
        return this.arguments;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return function.getSort();
    }
}
