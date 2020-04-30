/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class IntConstant extends Constant
{
  private final BigInteger value;

  private IntConstant(int value)
  {
    this.value = new BigInteger(String.valueOf(value));
  }

  public static IntConstant getInstance(int value)
  {
    return new IntConstant(value);
  }

  public static SmtExpr getSingletonTuple(int value)
  {
    SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE,
        new IntConstant(value));
    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(tuple);
    return singleton;
  }

  public static SmtExpr getSingletonTuple(IntConstant intConstant)
  {
    SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE,
        intConstant);
    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(tuple);
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
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return AbstractTranslator.intSort;
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    return this;
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof IntConstant))
    {
      return false;
    }
    IntConstant intConstant = (IntConstant) object;
    return value.equals(intConstant.value);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    return new ArrayList<>();
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    return this;
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }
    return this;
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this))
    {
      return true;
    }
    return false;
  }
}
