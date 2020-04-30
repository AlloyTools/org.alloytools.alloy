/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public class SetSort extends Sort
{
  public Sort elementSort;

  public SetSort(Sort elementSort)
  {
    super("Set", 0);
    this.elementSort = elementSort;
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

    if (!(object instanceof SetSort))
    {
      return false;
    }

    SetSort sort = (SetSort) object;
    return sort.elementSort.equals(this.elementSort);
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this) || elementSort.containsExpr(expr))
    {
      return true;
    }
    return false;
  }
}
