/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt;


import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class TranslatorUtils
{
  private static int freshNameIndex = 0;

  public static String sanitizeWithBars(Declaration declaration)
  {
    if (declaration.isOriginal())
    {
      // add extra space to separate original variables from generated ones
      return "|" + declaration.getName() + " |";
    }
    return declaration.getName();
  }

  public static String getFreshName(Sort sort)
  {
    freshNameIndex++;
    if (sort != null)
    {
      if (sort instanceof SetSort)
      {
        Sort elementSort = ((SetSort) sort).elementSort;
        if (elementSort instanceof TupleSort)
        {
          int arity = ((TupleSort) elementSort).elementSorts.size();
          if (arity > 1)
          {
            return "r" + arity + "." + freshNameIndex;
          }
        }
        return "s" + "." + freshNameIndex;
      }

      if (sort instanceof TupleSort)
      {
        int arity = ((TupleSort) sort).elementSorts.size();
        if (arity > 1)
        {
          return "t" + arity + "." + freshNameIndex;
        }
        Sort tupleSort = ((TupleSort) sort).elementSorts.get(0);
        if (tupleSort instanceof UninterpretedSort)
        {
          UninterpretedSort uninterpretedSort = (UninterpretedSort) tupleSort;

          if (uninterpretedSort.equals(AbstractTranslator.atomSort))
          {
            return "tA." + freshNameIndex;
          }

          if (uninterpretedSort.equals(AbstractTranslator.uninterpretedInt))
          {
            return "tU." + freshNameIndex;
          }
        }
        return "t" + "." + freshNameIndex;
      }

      if (sort instanceof UninterpretedSort)
      {
        UninterpretedSort uninterpretedSort = (UninterpretedSort) sort;

        if (uninterpretedSort.equals(AbstractTranslator.atomSort))
        {
          return "a." + freshNameIndex;
        }

        if (uninterpretedSort.equals(AbstractTranslator.uninterpretedInt))
        {
          return "u." + freshNameIndex;
        }
      }
    }
    return "x." + freshNameIndex;
  }

  public static void reset()
  {
    freshNameIndex = 0;
  }

  public static Sort getSetSortOfAtomWithArity(int n)
  {
    List<Sort> elementSorts = new ArrayList<>();
    for (int i = 0; i < n; ++i)
    {
      elementSorts.add(AbstractTranslator.atomSort);
    }
    return new SetSort(new TupleSort(elementSorts));
  }

  public static SmtExpr makeDistinct(SmtExpr... exprs)
  {
    if (exprs == null)
    {
      throw new RuntimeException();
    }
    else if (exprs.length == 1)
    {
      return exprs[0];
    }
    else
    {
      return new SmtMultiArityExpr(SmtMultiArityExpr.Op.DISTINCT, exprs);
    }
  }

  public static SmtExpr makeDistinct(List<SmtExpr> exprs)
  {
    if (exprs == null)
    {
      throw new RuntimeException();
    }
    else if (exprs.isEmpty() || exprs.size() == 1)
    {
      return BoolConstant.True;
    }
    else
    {
      return SmtMultiArityExpr.Op.DISTINCT.make(exprs);
    }
  }

  public static SmtExpr getTuple(Declaration... elements)
  {
    List<SmtExpr> smtExprs = Arrays.stream(elements)
                                   .map(Declaration::getVariable).collect(Collectors.toList());
    return SmtMultiArityExpr.Op.MKTUPLE.make(smtExprs);
  }

  public static SmtExpr getTuple(SmtExpr... smtExprs)
  {
    return new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, smtExprs);
  }

  public static int getInt(FunctionDefinition definition)
  {
    return getInt(definition.smtExpr);
  }

  public static int getInt(SmtExpr smtExpr)
  {
    SmtUnaryExpr unary = (SmtUnaryExpr) smtExpr;
    if (unary.getOp() == SmtUnaryExpr.Op.EMPTYSET)
    {
      return 0; // zero is equivalent to an empty set
    }
    assert (SmtUnaryExpr.Op.SINGLETON == unary.getOp());
    SmtMultiArityExpr tuple = (SmtMultiArityExpr) unary.getExpr();
    assert (SmtMultiArityExpr.Op.MKTUPLE == tuple.getOp());
    IntConstant constant = (IntConstant) tuple.getExprs().get(0);
    return Integer.parseInt(constant.getValue());
  }

  public static Set<Integer> getIntSet(FunctionDefinition definition)
  {
    return getIntSet(definition.getBody());
  }

  public static Set<Integer> getIntSet(SmtExpr smtExpr)
  {
    if (smtExpr instanceof SmtUnaryExpr)
    {
      return new HashSet<>(Arrays.asList(getInt(smtExpr)));
    }
    SmtBinaryExpr binary = (SmtBinaryExpr) smtExpr;
    Set<Integer> set = new HashSet<>();
    assert (binary.getOp() == SmtBinaryExpr.Op.UNION);
    set.addAll(getIntSet(binary.getA()));
    set.addAll(getIntSet(binary.getB()));
    return set;
  }

  public static Set<String> getAtomSet(FunctionDefinition definition)
  {
    return getAtomSet(definition.getBody());
  }

  public static Set<String> getAtomSet(SmtExpr smtExpr)
  {
    if (smtExpr instanceof UninterpretedConstant)
    {
      UninterpretedConstant constant = (UninterpretedConstant) smtExpr;
      return Collections.singleton(constant.getName());
    }
    if (smtExpr instanceof SmtUnaryExpr)
    {
      SmtUnaryExpr unary = (SmtUnaryExpr) smtExpr;
      if (unary.getOp() == SmtUnaryExpr.Op.EMPTYSET)
      {
        return new HashSet<>();
      }
      assert (SmtUnaryExpr.Op.SINGLETON == unary.getOp());
      SmtMultiArityExpr tuple = (SmtMultiArityExpr) unary.getExpr();
      assert (SmtMultiArityExpr.Op.MKTUPLE == tuple.getOp());
      UninterpretedConstant constant = (UninterpretedConstant) tuple.getExprs().get(0);
      return new HashSet<>(Collections.singletonList(constant.getName()));
    }
    if (smtExpr instanceof SmtBinaryExpr)
    {
      SmtBinaryExpr binary = (SmtBinaryExpr) smtExpr;
      Set<String> set = new HashSet<>();
      assert (binary.getOp() == SmtBinaryExpr.Op.UNION);
      set.addAll(getAtomSet(binary.getA()));
      set.addAll(getAtomSet(binary.getB()));
      return set;
    }

    throw new UnsupportedOperationException("Not supported yet");
  }

  public static Set<List<String>> getRelation(FunctionDefinition definition)
  {
    if (!(definition.getSort() instanceof SetSort))
    {
      throw new UnsupportedOperationException(definition.getSort().toString());
    }
    SetSort setSort = (SetSort) definition.getSort();
    if (!(setSort.elementSort instanceof TupleSort))
    {
      throw new UnsupportedOperationException(setSort.elementSort.toString());
    }
    return getRelation(definition.getBody());
  }

  public static Set<List<String>> getRelation(SmtExpr smtExpr)
  {
    if (smtExpr instanceof SmtUnaryExpr)
    {
      SmtUnaryExpr unary = (SmtUnaryExpr) smtExpr;
      if (unary.getOp() == SmtUnaryExpr.Op.EMPTYSET)
      {
        return new HashSet<>();
      }
      assert (SmtUnaryExpr.Op.SINGLETON == unary.getOp());
      SmtMultiArityExpr tupleExpression = (SmtMultiArityExpr) unary.getExpr();
      assert (SmtMultiArityExpr.Op.MKTUPLE == tupleExpression.getOp());
      List<String> tuple = new ArrayList<>();

      for (SmtExpr expr : tupleExpression.getExprs())
      {
        if (expr instanceof IntConstant)
        {
          tuple.add(((IntConstant) expr).getValue());
        }
        else if (expr instanceof UninterpretedConstant)
        {
          tuple.add(((UninterpretedConstant) expr).getName());
        }
        else
        {
          throw new UnsupportedOperationException(expr.toString());
        }
      }
      return new HashSet<>(Collections.singletonList(tuple));
    }
    SmtBinaryExpr binary = (SmtBinaryExpr) smtExpr;
    Set<List<String>> set = new HashSet<>();
    assert (binary.getOp() == SmtBinaryExpr.Op.UNION);
    set.addAll(getRelation(binary.getA()));
    set.addAll(getRelation(binary.getB()));
    return set;
  }


  public static FunctionDefinition getFunctionDefinition(SmtModel smtModel, String name)
  {
    FunctionDefinition definition = (FunctionDefinition) smtModel
        .getFunctions().stream()
        .filter(f -> f.getName().equals(name)).findFirst().get();
    definition = smtModel.evaluateUninterpretedInt(definition);
    return definition;
  }

  public static String getFriendlyAtom(String uninterpretedConstant, String replacement)
  {
    return uninterpretedConstant.replaceFirst("@uc_Atom_", replacement);
  }

  public static String getOriginalName(String name)
  {
    return name.replaceAll("\\|", "");
  }

  public static SmtExpr makeRelationFromDeclarations(List<SmtVariable> declarations)
  {
    List<SmtExpr> variables = declarations
        .stream().map(v -> v.getVariable()).collect(Collectors.toList());
    return TranslatorUtils.makeRelation(variables);
  }

  public static SmtExpr makeRelation(List<SmtExpr> smtExprs)
  {
    if (smtExprs.isEmpty())
    {
      throw new RuntimeException("Empty list");
    }

    SmtExpr set = makeRelation(smtExprs.get(smtExprs.size() - 1));
    for (int i = smtExprs.size() - 2; i >= 0; i--)
    {
      SmtExpr smtExpr = smtExprs.get(i);
      if (smtExpr.getSort() instanceof SetSort)
      {
        set = SmtBinaryExpr.Op.UNION.make(smtExpr, set);
      }
      else if (smtExpr.getSort() instanceof TupleSort)
      {
        set = SmtMultiArityExpr.Op.INSERT.make(smtExpr, set);
      }
      else
      {
        SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(smtExpr);
        set = SmtMultiArityExpr.Op.INSERT.make(tuple, set);
      }
    }
    return set;
  }

  public static SmtExpr makeRelation(SmtExpr smtExpr)
  {
    if ((smtExpr.getSort() instanceof UninterpretedSort) || smtExpr.getSort() instanceof IntSort)
    {
      SmtMultiArityExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, smtExpr);
      return SmtUnaryExpr.Op.SINGLETON.make(tuple);
    }
    else if (smtExpr.getSort() instanceof TupleSort)
    {
      return SmtUnaryExpr.Op.SINGLETON.make(smtExpr);
    }
    else
    {
      return smtExpr;
    }
  }

  public static List<SmtVariable> copySmtVariables(List<SmtVariable> smtVariables)
  {
    List<SmtVariable> newVariables = new ArrayList<>();
    for (SmtVariable smtVariable : smtVariables)
    {
      SmtVariable newVariable = new SmtVariable(TranslatorUtils.getFreshName(smtVariable.getSort()), smtVariable.getSort(), false);
      if (smtVariable.getConstraint() != null)
      {
        SmtExpr newConstraint = smtVariable.getConstraint()
                                           .substitute(smtVariable.getVariable(), newVariable.getVariable());
        newVariable.setConstraint(newConstraint);
      }
      newVariables.add(newVariable);
    }
    return newVariables;
  }

  public static SmtExpr getVariablesConstraints(List<SmtVariable> smtVariables)
  {
    SmtExpr andExpr = BoolConstant.True;
    for (SmtVariable smtVariable : smtVariables)
    {
      if (smtVariable.getConstraint() == null)
      {
        continue;
      }
      andExpr = SmtMultiArityExpr.Op.AND.make(andExpr, smtVariable.getConstraint());
    }
    return andExpr;
  }
}
