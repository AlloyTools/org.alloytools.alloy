/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import java.math.BigInteger;

public class IntConstant extends Expression
{
    private final BigInteger value;
    
    public IntConstant(BigInteger value)
    {
        this.value = value;
    }
    
    public IntConstant(int value)
    {
        this.value = new BigInteger(String.valueOf(value));
    }
    
    public IntConstant(String value)
    {
        this.value = new BigInteger(value);
    }  
    
    public String getValue()
    {
        return this.value.toString();
    }
    
    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
    
}
