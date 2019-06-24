/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.Map;

public class BoolConstant extends Constant
{
    private final boolean value;

    public static final BoolConstant True = new BoolConstant(true);
    public static final BoolConstant False = new BoolConstant(false);
    
    private BoolConstant(boolean value)
    {
        this.value = value;
    }
    
    public String getValue()
    {
        return String.valueOf(this.value);
    }

    public boolean getBooleanValue()
    {
        return value;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return AbstractTranslator.boolSort;
    }
    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        return this;
    }
    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof BoolConstant))
        {
            return false;
        }
        BoolConstant booleanObject = (BoolConstant) object;
        return value == booleanObject.value;
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
