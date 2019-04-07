/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;

import java.util.Map;

public class BoolConstant extends Constant
{
    private final boolean value;
    
    public BoolConstant(boolean value)
    {
        this.value = value;
    }
    
    public String getValue()
    {
        return String.valueOf(this.value);
    }   

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return Alloy2SmtTranslator.boolSort;
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
}
