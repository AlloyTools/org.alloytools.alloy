/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SmtLetExpr extends SmtExpr
{
  private final SmtExpr expr;
  private final Map<SmtVariable, SmtExpr> letVariables;

  public SmtLetExpr(Map<SmtVariable, SmtExpr> letVars, SmtExpr expr)
  {
    this.letVariables = new HashMap<>();
    this.expr = expr;
    for (Map.Entry<SmtVariable, SmtExpr> var : letVars.entrySet())
    {
      this.letVariables.put(var.getKey(), var.getValue());
    }
    checkTypes();
  }

  @Override
  protected void checkTypes()
  {
    // make sure the types of the declared variables match their corresponding expressions

    for (Map.Entry<SmtVariable, SmtExpr> entry : letVariables.entrySet())
    {
      if (!entry.getKey().getSort().equals(entry.getValue().getSort()))
      {
        throw new RuntimeException(String.format("The variable '%1$s' has sort '%2$s' which is the different than '%3$s', the sort of its expression", entry.getKey().getName(), entry.getKey().getSort(), entry.getValue().getSort()));
      }
    }

    // check there is no typing error within the body
    expr.checkTypes();
  }

  public Map<SmtVariable, SmtExpr> getLetVariables()
  {
    return this.letVariables;
  }

  public SmtExpr getSmtExpr()
  {
    return this.expr;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return expr.getSort();
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean equals(Object object)
  {
    // syntax equality without alpha equivalence
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof SmtLetExpr))
    {
      return false;
    }
    SmtLetExpr letObject = (SmtLetExpr) object;
    return letVariables.equals(letObject.letVariables) && expr.equals(letObject.expr);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = expr.getFreeVariables();
    for (Map.Entry<SmtVariable, SmtExpr> entry : letVariables.entrySet())
    {
      freeVariables.remove(entry.getKey().getVariable());
    }
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    List<SmtExpr> variables = letVariables.keySet()
                                          .stream()
                                          .map(v -> v.getVariable())
                                          .collect(Collectors.toList());
    // oldSmtExpr is not free
    if(variables.contains(oldSmtExpr))
    {
      // oldSmtExpr is not free
      return this;
    }
    else
    {
      if(variables.contains(newSmtExpr))
      {
        // the newSmtExpr should be free
        throw new UnsupportedOperationException(String.format("Expr '%1$s' is not free in '%2$s', " +
            "therefore it can not be replaced with '%3$s'.", newSmtExpr, this, oldSmtExpr));
      }

      Map<SmtVariable, SmtExpr> newMap = new HashMap<>();
      for (Map.Entry<SmtVariable, SmtExpr> entry: letVariables.entrySet())
      {
        newMap.put(entry.getKey(), entry.getValue().replace(oldSmtExpr, newSmtExpr));
      }
      SmtExpr newExpr = this.expr.replace(oldSmtExpr, newSmtExpr);
      return new SmtLetExpr(newMap, newExpr);
    }
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this) || this.expr.containsExpr(expr))
    {
      return true;
    }

    return false;
  }
}
