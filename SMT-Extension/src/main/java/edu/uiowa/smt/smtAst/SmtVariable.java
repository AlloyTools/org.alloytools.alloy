/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public class SmtVariable extends Declaration
{
  private SmtExpr constraint;

  public SmtVariable(String name, Sort sort, boolean isOriginal)
  {
    super(name, sort, isOriginal);
  }

  public void setConstraint(SmtExpr constraint)
  {
    this.constraint = constraint;
  }

  public SmtExpr getConstraint()
  {
    return constraint;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }
}
