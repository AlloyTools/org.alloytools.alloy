/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public class IntSort extends Sort
{
  private static IntSort instance = new IntSort();

  private IntSort()
  {
    super("Int", 0);
  }

  public static IntSort getInstance()
  {
    return instance;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof IntSort))
    {
      return false;
    }
    return true;
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
