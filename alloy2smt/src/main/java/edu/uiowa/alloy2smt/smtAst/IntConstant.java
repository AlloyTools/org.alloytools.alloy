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

import java.math.BigInteger;

public class IntConstant extends Expression
{
    private final BigInteger value;
    
    public IntConstant(BigInteger value)
    {
        this.value = value;
    }
    
    private IntConstant(int value)
    {
        this.value = new BigInteger(String.valueOf(value));
    }

    public static IntConstant getInstance(int value)
    {
        return new IntConstant(value);
    }

    public static Expression getSingletonTuple(int value)
    {
        Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                new IntConstant(value));
        Expression singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }

    public static Expression getSingletonTuple(IntConstant intConstant)
    {
        Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                intConstant);
        Expression singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
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

    @Override
    public Sort getSort()
    {
        return Alloy2SmtTranslator.intSort;
    }
}
