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
    }
    
    public FunctionCallExpression(FunctionDeclaration function, List<Expression> arguments)
    {
        this.function = function;
        this.arguments      = arguments;
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
    public Sort getSort() throws Exception
    {
        return function.getSort();
    }
}
