/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;

import java.util.*;
import java.util.stream.Collectors;

public class SmtMultiArityExpr extends SmtExpr
{
  private final Op op;
  private final List<SmtExpr> exprs;

  private SmtMultiArityExpr(Op op, List<SmtExpr> exprs)
  {
    this.op = op;
    this.exprs = exprs;

    if (this.exprs.stream().anyMatch(Objects::isNull))
    {
      throw new RuntimeException("One of the expression is null");
    }
    checkTypes();
  }

  public void checkTypes()
  {
    switch (op)
    {
      case MKTUPLE:
      {
        if (exprs.size() == 0)
        {
          throw new RuntimeException("mkTuple operation requires at least one expression");
        }
        break;
      }
      case INSERT:
      {
        if (exprs.size() <= 1)
        {
          throw new RuntimeException("Insert operation requires at least two expressions");
        }
        // the last expression should have a set sort
        SmtExpr setSmtExpr = exprs.get(exprs.size() - 1);
        if (!(setSmtExpr.getSort() instanceof SetSort))
        {
          throw new RuntimeException(String.format("The expression '%1$s' has sort '%2S' which is not set", setSmtExpr, setSmtExpr.getSort()));
        }
        SetSort setSort = (SetSort) setSmtExpr.getSort();

        // all remaining expressions should have the same sort of the elements of the set
        for (int i = 0; i < exprs.size() - 1; i++)
        {
          SmtExpr smtExpr = exprs.get(i);
          if (!(smtExpr.getSort().equals(setSort.elementSort)))
          {
            throw new RuntimeException(String.format("The sort '%1$s' of expression '%2$s' doesn't match the elements sort '%3$s'", exprs.get(i).getSort(), smtExpr, setSort.elementSort));
          }
        }
      }
      break;
      case DISTINCT:
      {
        if (exprs.size() <= 1)
        {
          throw new RuntimeException("distinct operation requires at least two expressions");
        }

        List<Sort> sorts = this.exprs.stream()
                                     .map(SmtExpr::getSort).collect(Collectors.toList());
        Sort firstSort = sorts.get(0);
        for (int i = 1; i < sorts.size(); i++)
        {
          if (!sorts.get(i).equals(firstSort))
          {
            throw new RuntimeException(String.format("Expressions of distinct operation do not have the same type:\n%s", sorts));
          }
        }
      }
      break;
      case OR:
      {
        checkBoolType(Op.OR);
      }
      break;
      case AND:
      {
        checkBoolType(Op.AND);
      }
      break;
      default:
        throw new UnsupportedOperationException();
    }
  }

  private void checkBoolType(Op op)
  {
    if (exprs.size() == 0)
    {
      throw new RuntimeException(op + " operation requires at least one expression");
    }

    // all expressions should have boolean sort
    for (SmtExpr smtExpr : exprs)
    {
      if (!(smtExpr.getSort().equals(AbstractTranslator.boolSort)))
      {
        throw new RuntimeException(String.format("The sort '%1$s' of expression '%2$s' is not boolean", smtExpr.getSort(), smtExpr));
      }
    }
  }

  public SmtMultiArityExpr(Op op, SmtExpr... exprs)
  {
    this(op, Arrays.asList(exprs));
  }

  public Op getOp()
  {
    return this.op;
  }

  public List<SmtExpr> getExprs()
  {
    return this.exprs;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  public SmtExpr get(int index)
  {
    assert (0 <= index && index < exprs.size());
    return this.exprs.get(index);
  }

  public enum Op
  {
    MKTUPLE("mkTuple"),
    INSERT("insert"),
    DISTINCT("distinct"),
    OR("or"),
    AND("and");

    private final String opStr;

    Op(String op)
    {
      this.opStr = op;
    }

    public SmtMultiArityExpr make(List<SmtExpr> exprs)
    {
      return new SmtMultiArityExpr(this, exprs);
    }

    public SmtMultiArityExpr make(SmtExpr... exprs)
    {
      return new SmtMultiArityExpr(this, exprs);
    }

    public static Op getOp(String operator)
    {
      switch (operator)
      {
        case "mkTuple":
          return MKTUPLE;
        case "insert":
          return INSERT;
        case "distinct":
          return DISTINCT;
        case "or":
          return OR;
        case "and":
          return AND;
        default:
          throw new UnsupportedOperationException("Operator " + operator + " is not defined");
      }
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
      case MKTUPLE:
      {

        List<Sort> sorts = new ArrayList<>();
        for (SmtExpr expr : exprs)
        {
          sorts.add(expr.getSort());
        }
        return new TupleSort(sorts);
      }
      case INSERT:
      {
        // return the sort of the last element
        return exprs.get(exprs.size() - 1).getSort();
      }
      case DISTINCT:
      case OR:
      case AND:
        return AbstractTranslator.boolSort;
      default:
        throw new UnsupportedOperationException();
    }
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    List<SmtExpr> smtExprs = new ArrayList<>();
    for (SmtExpr smtExpr : this.exprs)
    {
      smtExprs.add(smtExpr.evaluate(functions));
    }
    return new SmtMultiArityExpr(this.op, smtExprs);
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof SmtMultiArityExpr))
    {
      return false;
    }
    SmtMultiArityExpr multiArity = (SmtMultiArityExpr) object;
    return op == multiArity.op &&
        exprs.equals(multiArity.exprs);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = new ArrayList<>();
    for (SmtExpr smtExpr : exprs)
    {
      freeVariables.addAll(smtExpr.getFreeVariables());
    }
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    List<SmtExpr> newSmtExprs = new ArrayList<>();
    for (SmtExpr smtExpr : exprs)
    {
      if (smtExpr.equals(newVariable))
      {
        throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
      }
      newSmtExprs.add(smtExpr.substitute(oldVariable, newVariable));
    }
    return new SmtMultiArityExpr(op, newSmtExprs);
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }

    List<SmtExpr> newSmtExprs = new ArrayList<>();
    for (SmtExpr smtExpr : exprs)
    {
      newSmtExprs.add(smtExpr.replace(oldSmtExpr, newSmtExpr));
    }
    return new SmtMultiArityExpr(op, newSmtExprs);
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this))
    {
      return true;
    }

    for (SmtExpr smtExpr: this.exprs)
    {
      if(smtExpr.containsExpr(expr))
      {
        return true;
      }
    }

    return false;
  }
}
