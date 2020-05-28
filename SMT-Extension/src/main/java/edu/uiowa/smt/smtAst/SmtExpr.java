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

  public abstract Sort getSort();

  public String getComment()
  {
    return this.comment;
  }

  public void setComment(String comment)
  {
    this.comment = comment;
  }

  @Override
  public String toString()
  {
    SmtLibPrinter printer = new SmtLibPrinter();
    printer.visit(this);
    return printer.getSmtLib();
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

  public SmtBinaryExpr implies(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.IMPLIES.make(this, expr);
  }

  public SmtBinaryExpr member(SmtExpr set)
  {
    return SmtBinaryExpr.Op.MEMBER.make(this, set);
  }

  public SmtBinaryExpr subset(SmtExpr set)
  {
    return SmtBinaryExpr.Op.SUBSET.make(this, set);
  }

  public SmtBinaryExpr product(SmtExpr set)
  {
    return SmtBinaryExpr.Op.PRODUCT.make(this, set);
  }

  public SmtBinaryExpr join(SmtExpr set)
  {
    return SmtBinaryExpr.Op.JOIN.make(this, set);
  }

  public SmtBinaryExpr plus(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.PLUS.make(this, expr);
  }

  public SmtBinaryExpr minus(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.MINUS.make(this, expr);
  }

  public SmtBinaryExpr multiply(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.MULTIPLY.make(this, expr);
  }

  public SmtBinaryExpr divide(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.DIVIDE.make(this, expr);
  }

  public SmtBinaryExpr mod(SmtExpr expr)
  {
    return SmtBinaryExpr.Op.MOD.make(this, expr);
  }

  public SmtUnaryExpr singleton()
  {
    return SmtUnaryExpr.Op.SINGLETON.make(this);
  }

  public SmtUnaryExpr not()
  {
    return SmtUnaryExpr.Op.NOT.make(this);
  }
}
