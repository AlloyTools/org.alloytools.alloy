/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.printers.SmtLibPrinter;

import java.util.Collections;
import java.util.List;
import java.util.Map;

public class Sort extends Expression
{
    private final String name;
    private final int    arity;

    public Sort(String name, int arity)
    {
        this.name   = name;
        this.arity  = arity;
    }

    public String getName()
    {
        return this.name;
    }

    @Override
    public String toString()
    {
        SmtLibPrinter printer = new SmtLibPrinter();
        printer.visit(this);
        return printer.getSmtLib();
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return this;
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        throw new UnsupportedOperationException();
    }
    @Override
    public boolean equals(Object object)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Variable> getFreeVariables()
    {
        return Collections.emptyList();
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        return this;
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        if(oldExpression.equals(this))
        {
            return newExpression;
        }
        return this;
    }
}
