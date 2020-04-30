/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public class ConstantDefinition extends FunctionDefinition
{
  public ConstantDefinition(String name, Sort outputSort, SmtExpr smtExpr, boolean isOriginal)
  {
    super(name, outputSort, smtExpr, isOriginal);
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }
}