/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtLibPrinter;

import java.util.List;
import java.util.Map;

public abstract class SmtExpr extends SmtAst
{
  private String comment = "";

  @Override
  public String toString()
  {
    SmtLibPrinter printer = new SmtLibPrinter();
    printer.visit(this);
    return printer.getSmtLib();
  }

  public abstract Sort getSort();

  public String getComment()
  {
    return this.comment;
  }

  public void setComment(String comment)
  {
    this.comment = comment;
  }


  protected void checkTypes()
  {
  }

  public abstract SmtExpr evaluate(Map<String, FunctionDefinition> functions);

  @Override
  public abstract boolean equals(Object object);

  public abstract List<Variable> getFreeVariables();

  public abstract SmtExpr substitute(Variable oldVariable, Variable newVariable);

  public abstract SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr);

  public abstract boolean containsExpr(SmtExpr expr);
}
