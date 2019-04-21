/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        FunctionDefinition definition = functions.get(this.function.getName());
        // improve the performance of this line
        Map<String, FunctionDefinition> newScope = new HashMap<>(functions);
        for(int i = 0; i < arguments.size(); i++)
        {
            Expression argument = arguments.get(i);
            if(argument instanceof UninterpretedConstant)
            {
                UninterpretedConstant uninterpretedConstant = (UninterpretedConstant) argument;
                String argumentName = definition.inputVariables.get(i).getName();
                // ToDo: refactor this
                // for now generate a new constant with the passed parameter;
                ConstantDefinition constant = new ConstantDefinition(argumentName, uninterpretedConstant.getSort(), uninterpretedConstant);
                newScope.put(constant.getName(), constant);
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }
        return definition.getExpression().evaluate(newScope);
    }
    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof FunctionCallExpression))
        {
            return false;
        }
        FunctionCallExpression functionCall = (FunctionCallExpression) object;
        return function.equals(functionCall.function) &&
                arguments.equals(functionCall.arguments);
    }
}
