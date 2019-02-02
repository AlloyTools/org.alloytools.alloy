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
    private final String            functionName;
    private final List<Expression>  arguments;

    public FunctionCallExpression(String functionName, Expression ... arguments)
    {
        this.functionName   = functionName;
        this.arguments      = Arrays.asList(arguments);
    }
    
    public FunctionCallExpression(String functionName, List<Expression> arguments)
    {
        this.functionName   = functionName;
        this.arguments      = arguments;
    }    

    public String getFunctionName()
    {
        return this.functionName;
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
        throw new UnsupportedOperationException("Function calls do not store yet function declarations");
    }
}
