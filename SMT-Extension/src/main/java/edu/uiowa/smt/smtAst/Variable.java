/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class Variable extends SmtExpr
{
  private final Declaration declaration;

  Variable(Declaration declaration)
  {
    this.declaration = declaration;
  }

  public String getName()
  {
    return this.declaration.getName();
  }

  public Declaration getDeclaration()
  {
    return this.declaration;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return declaration.getSort();
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof Variable))
    {
      return false;
    }
    Variable constantObject = (Variable) object;
    return declaration.equals(constantObject.declaration);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = new ArrayList<>();
    freeVariables.add(this);
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    if (this.equals(newVariable))
    {
      throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
    }
    if (this.equals(oldVariable))
    {
      return newVariable;
    }
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

  public boolean isOriginal()
  {
    return declaration.isOriginal();
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
