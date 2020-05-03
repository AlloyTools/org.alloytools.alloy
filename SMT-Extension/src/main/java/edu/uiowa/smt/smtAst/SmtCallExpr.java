/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.*;

public class SmtCallExpr extends SmtExpr
{
  private final FunctionDeclaration function;
  private final List<SmtExpr> arguments;

  public SmtCallExpr(FunctionDeclaration function, SmtExpr... arguments)
  {
    this.function = function;
    this.arguments = Arrays.asList(arguments);
    checkTypes();
  }

  public SmtCallExpr(FunctionDeclaration function, List<SmtExpr> arguments)
  {
    this.function = function;
    this.arguments = arguments;
    checkTypes();
  }

  @Override
  protected void checkTypes()
  {
    if (function.getInputSorts().size() != arguments.size())
    {
      throw new RuntimeException(String.format("Function '%1$s' expects %2$d arguments but %3$d arguments were passed", function.getName(), function.getInputSorts().size(), arguments.size()));
    }

    for (int i = 0; i < arguments.size(); i++)
    {
      Sort actualSort = arguments.get(i).getSort();
      Sort expectedSort = function.getInputSorts().get(i);
      if (!actualSort.equals(expectedSort))
      {
        throw new RuntimeException(String.format("Function '%1$s' expects argument %2$d to have sort '%3$s', but it has sort '%4$s'", function.getName(), i, expectedSort, actualSort));
      }
    }
  }

  public String getFunctionName()
  {
    return this.function.getName();
  }

  public List<SmtExpr> getArguments()
  {
    return this.arguments;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return function.getSort();
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    FunctionDefinition definition = functions.get(this.function.getName());
    // improve the performance of this line
    Map<String, FunctionDefinition> newScope = new HashMap<>(functions);
    for (int i = 0; i < arguments.size(); i++)
    {
      SmtExpr argument = arguments.get(i);
      if (argument instanceof UninterpretedConstant)
      {
        UninterpretedConstant uninterpretedConstant = (UninterpretedConstant) argument;
        String argumentName = definition.inputVariables.get(i).getName();
        // ToDo: refactor this
        // for now generate a new constant with the passed parameter;
        ConstantDefinition constant = new ConstantDefinition(argumentName, uninterpretedConstant.getSort(), uninterpretedConstant, true);
        newScope.put(constant.getName(), constant);
      }
      else
      {
        throw new UnsupportedOperationException();
      }
    }
    return definition.getBody().evaluate(newScope);
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof SmtCallExpr))
    {
      return false;
    }
    SmtCallExpr functionCall = (SmtCallExpr) object;
    return function.equals(functionCall.function) &&
        arguments.equals(functionCall.arguments);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = new ArrayList<>();
    for (SmtExpr smtExpr : arguments)
    {
      freeVariables.addAll(smtExpr.getFreeVariables());
    }
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    if (this.function.getVariable().equals(newVariable))
    {
      throw new UnsupportedOperationException();
    }

    List<SmtExpr> newSmtExprs = new ArrayList<>();
    for (SmtExpr smtExpr : arguments)
    {
      if (smtExpr.equals(newVariable))
      {
        throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
      }
      newSmtExprs.add(smtExpr.substitute(oldVariable, newVariable));
    }
    return new SmtCallExpr(function, newSmtExprs);
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }
    List<SmtExpr> newSmtExprs = new ArrayList<>();
    for (SmtExpr smtExpr : arguments)
    {
      newSmtExprs.add(smtExpr.replace(oldSmtExpr, newSmtExpr));
    }
    return new SmtCallExpr(function, newSmtExprs);
  }

  public FunctionDeclaration getFunction()
  {
    return function;
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this))
    {
      return true;
    }

    for (SmtExpr smtExpr: this.arguments)
    {
      if(smtExpr.containsExpr(expr))
      {
        return true;
      }
    }

    return false;
  }
}
