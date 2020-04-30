/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtLibPrinter;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class Sort extends SmtExpr
{
  private final String name;
  private final int arity;

  public Sort(String name, int arity)
  {
    this.name = name;
    this.arity = arity;
  }

  public String getName()
  {
    return this.name;
  }

  @Override
  public String toString()
  {
    SmtLibPrinter printer = new SmtLibPrinter();
    printer.visit(this);
    return printer.getSmtLib();
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return this;
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean equals(Object object)
  {
    throw new UnsupportedOperationException();
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
    throw new UnsupportedOperationException();
  }
}
