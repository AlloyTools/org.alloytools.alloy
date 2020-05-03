/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class SmtBinaryExpr extends SmtExpr
{
  private final Op op;
  private SmtExpr A;
  private SmtExpr B;

  private SmtBinaryExpr(Op op, SmtExpr A, SmtExpr B)
  {
    this.op = op;
    if (A == null)
    {
      throw new RuntimeException("Left expression is null");
    }
    this.A = A;
    if (B == null)
    {
      throw new RuntimeException("Right expression is null");
    }
    this.B = B;

    checkTypes();
  }

  @Override
  protected void checkTypes()
  {
    switch (op)
    {
      case IMPLIES:
      {
        if (A.getSort() != AbstractTranslator.boolSort)
        {
          throw new RuntimeException(String.format("Left expression sort '%1$s' is not boolean", A.getSort()));
        }
        if (B.getSort() != AbstractTranslator.boolSort)
        {
          throw new RuntimeException(String.format("Right expression sort '%1$s' is not boolean", B.getSort()));
        }
      }
      break;
      case PLUS:
      case MINUS:
      case MULTIPLY:
      case DIVIDE:
      case MOD:
      case GTE:
      case LTE:
      case GT:
      case LT:
      {
        if (A.getSort() != AbstractTranslator.intSort)
        {
          throw new RuntimeException(String.format("Left expression sort '%1$s' is not integer or  set of integers", A.getSort()));
        }
        if (B.getSort() != AbstractTranslator.intSort)
        {
          throw new RuntimeException(String.format("Right expression sort '%1$s' is not integer or  set of integers", B.getSort()));
        }
      }
      break;

      case EQ:
      case UNION:
      case INTERSECTION:
      case SETMINUS:
      case SUBSET:
      {
        if (!A.getSort().equals(B.getSort()))
        {
          throw new RuntimeException(String.format("The sort of left expression sort '%1$s' is different than the sort of right expression '%2$s'", A.getSort(), B.getSort()));
        }
      }
      break;

      case MEMBER:
      {
        if (B instanceof IntConstant)
        {
          B = IntConstant.getSingletonTuple((IntConstant) B);
        }

        if (!(B.getSort() instanceof SetSort))
        {
          throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set", B.getSort()));
        }

        SetSort setSort = (SetSort) B.getSort();

        if (!(A.getSort().equals(setSort.elementSort)))
        {
          throw new RuntimeException(String.format("The sort of left expression '%1$s' doesn't match the element sort of the right expression '%2$s'", A.getSort(), setSort.elementSort));
        }
      }
      break;

      case JOIN:
      {
        if (!(A.getSort() instanceof SetSort &&
            ((SetSort) A.getSort()).elementSort instanceof TupleSort))
        {
          throw new RuntimeException(String.format("The sort of left expression '%1$s' is not a set of tuples", A.getSort()));
        }
        if (!(B.getSort() instanceof SetSort &&
            ((SetSort) B.getSort()).elementSort instanceof TupleSort))
        {
          throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set of tuples", B.getSort()));
        }

        TupleSort leftSort = (TupleSort) ((SetSort) A.getSort()).elementSort;
        TupleSort rightSort = (TupleSort) ((SetSort) B.getSort()).elementSort;

        if (!(leftSort.elementSorts.get(leftSort.elementSorts.size() - 1).equals(rightSort.elementSorts.get(0))))
        {
          throw new RuntimeException(String.format("The left and right sorts ('%1$s' and '%2$s') can't be joined", leftSort, rightSort));
        }
      }
      break;
      case PRODUCT:
      {
        if (!(A.getSort() instanceof SetSort &&
            ((SetSort) A.getSort()).elementSort instanceof TupleSort))
        {
          throw new RuntimeException(String.format("The sort of left expression '%1$s' is not a set of tuples", A.getSort()));
        }
        if (!(B.getSort() instanceof SetSort &&
            ((SetSort) B.getSort()).elementSort instanceof TupleSort))
        {
          throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set of tuples", B.getSort()));
        }
      }
      break;
      case TUPSEL:
      {
        if (!(A instanceof IntConstant))
        {
          throw new RuntimeException(String.format("The left expression '%1$s' is not a constant integer", A));
        }
        if (!(B.getSort() instanceof TupleSort))
        {
          throw new RuntimeException(String.format("The sort of right expression '%1$s' is not tuple", B.getSort()));
        }

        int index = Integer.parseInt(((IntConstant) A).getValue());
        TupleSort sort = (TupleSort) B.getSort();
        if (index >= sort.elementSorts.size() || index < 0)
        {
          throw new RuntimeException(String.format("The index '%1$d' out of range", index));
        }
      }
      break;
      default:
        throw new UnsupportedOperationException();
    }
  }

  public SmtExpr getA()
  {
    return this.A;
  }

  public SmtExpr getB()
  {
    return this.B;
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
    IMPLIES("=>"),
    PLUS("+"),
    MINUS("-"),
    MULTIPLY("*"),
    DIVIDE("/"),
    MOD("mod"),
    EQ("="),
    GTE(">="),
    LTE("<="),
    GT(">"),
    LT("<"),
    UNION("union"),
    INTERSECTION("intersection"),
    SETMINUS("setminus"),
    MEMBER("member"),
    SUBSET("subset"),
    JOIN("join"),
    PRODUCT("product"),
    TUPSEL("tupSel");

    private final String opStr;

    public SmtBinaryExpr make(SmtExpr left, SmtExpr right)
    {
      return new SmtBinaryExpr(this, left, right);
    }

    Op(String op)
    {
      this.opStr = op;
    }

    public static Op getOp(String operator)
    {
      switch (operator)
      {
        case "=>":
          return IMPLIES;
        case "+":
          return PLUS;
        case "-":
          return MINUS;
        case "*":
          return MULTIPLY;
        case "/":
          return DIVIDE;
        case "mod":
          return MOD;
        case "=":
          return EQ;
        case ">=":
          return GTE;
        case "<=":
          return LTE;
        case ">":
          return GT;
        case "<":
          return LT;
        case "union":
          return UNION;
        case "intersection":
          return INTERSECTION;
        case "setminus":
          return SETMINUS;
        case "member":
          return MEMBER;
        case "subset":
          return SUBSET;
        case "join":
          return JOIN;
        case "product":
          return PRODUCT;
        case "tupSel":
          return TUPSEL;
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
      case IMPLIES:
        return AbstractTranslator.boolSort;
      case PLUS:
        return A.getSort() instanceof IntSort ? AbstractTranslator.intSort : AbstractTranslator.setOfUninterpretedIntTuple;
      case MINUS:
        return A.getSort() instanceof IntSort ? AbstractTranslator.intSort : AbstractTranslator.setOfUninterpretedIntTuple;
      case MULTIPLY:
        return A.getSort() instanceof IntSort ? AbstractTranslator.intSort : AbstractTranslator.setOfUninterpretedIntTuple;
      case DIVIDE:
        return A.getSort() instanceof IntSort ? AbstractTranslator.intSort : AbstractTranslator.setOfUninterpretedIntTuple;
      case MOD:
        return A.getSort() instanceof IntSort ? AbstractTranslator.intSort : AbstractTranslator.setOfUninterpretedIntTuple;
      case EQ:
        return AbstractTranslator.boolSort;
      case GTE:
        return AbstractTranslator.boolSort;
      case LTE:
        return AbstractTranslator.boolSort;
      case GT:
        return AbstractTranslator.boolSort;
      case LT:
        return AbstractTranslator.boolSort;
      case UNION:
        return A.getSort();
      case INTERSECTION:
        return A.getSort();
      case SETMINUS:
        return A.getSort();
      case MEMBER:
        return AbstractTranslator.boolSort;
      case SUBSET:
        return AbstractTranslator.boolSort;
      case JOIN:
      {
        // type checking is handled during construction

        TupleSort leftSort = (TupleSort) ((SetSort) A.getSort()).elementSort;
        TupleSort rightSort = (TupleSort) ((SetSort) B.getSort()).elementSort;

        // the join sorts should match
        assert (leftSort.elementSorts.get(leftSort.elementSorts.size() - 1) ==
            rightSort.elementSorts.get(0));

        List<Sort> newSorts = new ArrayList<>();
        for (int i = 0; i < leftSort.elementSorts.size() - 1; i++)
        {
          newSorts.add(leftSort.elementSorts.get(i));
        }

        for (int i = 1; i < rightSort.elementSorts.size(); i++)
        {
          newSorts.add(rightSort.elementSorts.get(i));
        }

        Sort sort = new SetSort(new TupleSort(newSorts));

        return sort;
      }
      case PRODUCT:
      {
        // type checking is handled during construction

        TupleSort leftSort = (TupleSort) ((SetSort) A.getSort()).elementSort;
        TupleSort rightSort = (TupleSort) ((SetSort) B.getSort()).elementSort;

        List<Sort> newSorts = new ArrayList<>();
        newSorts.addAll(leftSort.elementSorts);
        newSorts.addAll(rightSort.elementSorts);

        Sort sort = new SetSort(new TupleSort(newSorts));
        return sort;
      }
      case TUPSEL:
      {
        int index = Integer.parseInt(((IntConstant) A).getValue());
        TupleSort sort = (TupleSort) B.getSort();
        return sort.elementSorts.get(index);
      }
      default:
        throw new UnsupportedOperationException();
    }
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    switch (op)
    {
      case EQ:
      {
        if (A instanceof Variable && B instanceof UninterpretedConstant)
        {
          return evaluateEquality(functions, A, B);
        }
        if (B instanceof Variable && A instanceof UninterpretedConstant)
        {
          return evaluateEquality(functions, B, A);
        }
      }
      break;
      case UNION:
      {
        SmtExpr left = A.evaluate(functions);
        SmtExpr right = B.evaluate(functions);
        return Op.UNION.make(left, right);
      }
    }
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof SmtBinaryExpr))
    {
      return false;
    }
    SmtBinaryExpr binaryObject = (SmtBinaryExpr) object;
    return op == binaryObject.op &&
        A.equals(binaryObject.A) &&
        B.equals(binaryObject.B);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = A.getFreeVariables();
    freeVariables.addAll(B.getFreeVariables());
    return freeVariables;
  }

  private SmtExpr evaluateEquality(Map<String, FunctionDefinition> functions, SmtExpr left, SmtExpr right)
  {
    String variableName = ((Variable) left).getName();
    if (!functions.containsKey(variableName))
    {
      throw new RuntimeException("Function " + variableName + " is undefined");
    }
    SmtExpr leftValue = functions.get(variableName).getBody();
    boolean isEqual = leftValue.equals(right);
    if (isEqual)
    {
      return BoolConstant.True;
    }
    else
    {
      return BoolConstant.False;
    }
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    if (A.equals(newVariable) || B.equals(newVariable))
    {
      throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
    }

    SmtExpr A = this.A.substitute(oldVariable, newVariable);
    SmtExpr B = this.B.substitute(oldVariable, newVariable);
    return op.make(A, B);
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }
    SmtExpr A = this.A.replace(oldSmtExpr, newSmtExpr);
    SmtExpr B = this.B.replace(oldSmtExpr, newSmtExpr);
    return op.make(A, B);
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this) || A.containsExpr(expr) || B.containsExpr(expr))
    {
      return true;
    }
    return false;
  }
}
