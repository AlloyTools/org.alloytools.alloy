/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SmtQtExpr extends SmtExpr
{
  private final SmtExpr expr;
  private final List<SmtVariable> variables;
  private final Op op;

  private SmtQtExpr(Op op, List<SmtVariable> variables, SmtExpr expr)
  {
    this.variables = new ArrayList<>();
    this.expr = expr;
    this.op = op;
    for (SmtVariable bdVar : variables)
    {
      this.variables.add(bdVar);
    }
    checkTypes();
  }

  @Override
  protected void checkTypes()
  {
    if (expr.getSort() != AbstractTranslator.boolSort)
    {
      throw new RuntimeException(String.format("The sort '%1$s' of the quantified expression is not boolean", expr.getSort()));
    }
    if (variables.size() == 0)
    {
      throw new RuntimeException(String.format("Expected at least one variable for the quantified expression '%1$s'.", this.toString()));
    }
  }

  private SmtQtExpr(Op op, SmtExpr expr, SmtVariable... variables)
  {
    this.variables = Arrays.asList(variables);
    this.expr = expr;
    this.op = op;
  }

  public List<SmtVariable> getVariables()
  {
    return this.variables;
  }

  public SmtExpr getExpr()
  {
    return this.expr;
  }

  public Op getOp()
  {
    return this.op;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  public enum Op
  {
    FORALL("forall"),
    EXISTS("exists");

    private final String opStr;

    Op(String op)
    {
      this.opStr = op;
    }

    public static Op getOp(String operator)
    {
      switch (operator)
      {
        case "forall":
          return FORALL;
        case "exists":
          return EXISTS;
        default:
          throw new UnsupportedOperationException("Operator " + operator + " is not defined");
      }
    }

    public SmtQtExpr make(SmtExpr expr, SmtVariable... variables)
    {
      return new SmtQtExpr(this, expr, variables);
    }

    public SmtQtExpr make(SmtExpr expr, List<SmtVariable> variables)
    {
      return new SmtQtExpr(this, variables, expr);
    }

    @Override
    public String toString()
    {
      return this.opStr;
    }
  }

  @Override
  public Sort getSort()
  {
    switch (op)
    {
      case EXISTS:
      case FORALL:
        return AbstractTranslator.boolSort;
      default:
        throw new UnsupportedOperationException("Unsupported operator" + op.toString());
    }
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
    if (!(object instanceof SmtQtExpr))
    {
      return false;
    }
    SmtQtExpr quantifiedObject = (SmtQtExpr) object;
    if (!variables.equals(quantifiedObject.variables))
    {
      return false;
    }
    return op == quantifiedObject.op &&
        expr.equals(quantifiedObject.expr);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = expr.getFreeVariables();
    freeVariables.removeAll(variables.stream().map(v -> v.getVariable()).collect(Collectors.toList()));
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    SmtExpr body = expr;
    List<SmtVariable> variables = new ArrayList<>(this.variables);
    // check if the new variable is declared
    for (Declaration declaration : this.variables)
    {
      if (declaration.getVariable().equals(newVariable))
      {
        // choose a new name for the declared variable
        SmtVariable newDeclaration = new SmtVariable(TranslatorUtils.getFreshName(declaration.getSort()), declaration.getSort(), false);
        if (declaration instanceof SmtVariable)
        {
          SmtExpr constraint = ((SmtVariable) declaration).getConstraint();
          SmtExpr newConstraint = constraint.substitute(oldVariable, newVariable);
          newDeclaration.setConstraint(newConstraint);
        }
        else
        {
          throw new UnsupportedOperationException();
        }
        body = expr.substitute(declaration.getVariable(), newDeclaration.getVariable());
        variables.remove(declaration);
        variables.add(newDeclaration);
      }
    }
    if (expr.equals(newVariable))
    {
      throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
    }

    SmtExpr newSmtExpr = body.substitute(oldVariable, newVariable);
    return new SmtQtExpr(op, variables, newSmtExpr);
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }
    SmtExpr smtExpr = expr.replace(oldSmtExpr, newSmtExpr);
    return new SmtQtExpr(op, variables, smtExpr);
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
