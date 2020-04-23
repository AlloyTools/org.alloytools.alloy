/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public class Assertion extends SmtAst
{
  private final SmtExpr smtExpr;

  private final String comment;

  private final String symbolicName;

  public Assertion(String symbolicName, String comment, SmtExpr smtExpr)
  {
    this.symbolicName = symbolicName;
    this.comment = comment;
    this.smtExpr = smtExpr;
  }

  public String getComment()
  {
    return this.comment;
  }

  public SmtExpr getSmtExpr()
  {
    return this.smtExpr;
  }

  public String getSymbolicName()
  {
    return symbolicName;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }
}
