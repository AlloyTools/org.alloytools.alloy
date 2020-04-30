/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.SmtEnv;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

public class ExprTranslator
{
  final Alloy2SmtTranslator translator;

  final ExprUnaryTranslator exprUnaryTranslator;

  final ExprBinaryTranslator exprBinaryTranslator;

  final ExprQtTranslator exprQtTranslator;

  final ExprCallTranslator exprCallTranslator;

  final ExprLetTranslator exprLetTranslator;

  final ExprVarTranslator exprVarTranslator;

  final DeclTranslator declTranslator;

  public ExprTranslator(Alloy2SmtTranslator translator)
  {
    this.translator = translator;
    this.exprVarTranslator = new ExprVarTranslator(this);
    this.exprUnaryTranslator = new ExprUnaryTranslator(this);
    this.exprBinaryTranslator = new ExprBinaryTranslator(this);
    this.exprQtTranslator = new ExprQtTranslator(this);
    this.exprCallTranslator = new ExprCallTranslator(this);
    this.exprLetTranslator = new ExprLetTranslator(this);
    this.declTranslator = new DeclTranslator(this);
  }

  public SmtExpr translateFormula(String label, Expr expr)
  {
    assert (expr.type() == Type.FORMULA);
    SmtEnv smtEnv = new SmtEnv();
    SmtExpr formula = translateExpr(expr, smtEnv);
    formula = addAuxiliaryVariables(formula, smtEnv);
    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(expr.pos), label, formula);
    translator.smtScript.addAssertion(assertion);
    return formula;
  }

  public SmtExpr addAuxiliaryVariables(SmtExpr booleanSmtExpr, SmtEnv smtEnv)
  {
    assert (booleanSmtExpr.getSort().equals(AbstractTranslator.boolSort));
    List<SmtVariable> variables = smtEnv.getAuxiliaryVariables();
    if (!variables.isEmpty())
    {
      SmtExpr constraints = TranslatorUtils.getVariablesConstraints(variables);
      SmtExpr body = SmtMultiArityExpr.Op.AND.make(constraints, booleanSmtExpr);
      booleanSmtExpr = SmtQtExpr.Op.EXISTS.make(body, variables);
    }
    return booleanSmtExpr;
  }

  SmtExpr translateExpr(Expr expr, SmtEnv smtEnv)
  {
    if (expr instanceof Sig || expr instanceof Sig.Field)
    {
      return getExpression(expr, exprUnaryTranslator.translateExprUnary((ExprUnary) ExprUnary.Op.NOOP.make(null, expr), smtEnv));
    }
    if (expr instanceof ExprVar)
    {
      return getExpression(expr, exprVarTranslator.translateExprVar((ExprVar) expr, smtEnv));
    }
    if (expr instanceof ExprUnary)
    {
      return getExpression(expr, exprUnaryTranslator.translateExprUnary((ExprUnary) expr, smtEnv));
    }
    else if (expr instanceof ExprBinary)
    {
      return getExpression(expr, exprBinaryTranslator.translateExprBinary((ExprBinary) expr, smtEnv));
    }
    else if (expr instanceof ExprQt)
    {
      return getExpression(expr, exprQtTranslator.translateExprQt((ExprQt) expr, smtEnv));
    }
    else if (expr instanceof ExprConstant)
    {
      return getExpression(expr, translateExprConstant((ExprConstant) expr, smtEnv));
    }
    else if (expr instanceof ExprList)
    {
      return getExpression(expr, translateExprList((ExprList) expr, smtEnv));
    }
    else if (expr instanceof ExprCall)
    {
      return getExpression(expr, exprCallTranslator.translateExprCall((ExprCall) expr, smtEnv));
    }
    else if (expr instanceof ExprITE)
    {
      return getExpression(expr, translateExprITE((ExprITE) expr, smtEnv));
    }
    else if (expr instanceof ExprLet)
    {
      return getExpression(expr, exprLetTranslator.translateExprLet((ExprLet) expr, smtEnv));
    }

    throw new UnsupportedOperationException(expr.toString());
  }

  private SmtExpr getExpression(Expr expr, SmtExpr smtExpr)
  {
    smtExpr.setComment(expr.toString());
    return smtExpr;
  }

  public SmtExpr translateExprITE(ExprITE expr, SmtEnv smtEnv)
  {
    SmtExpr condExpr = translateExpr(expr.cond, smtEnv);
    SmtExpr thenExpr = translateExpr(expr.left, smtEnv);
    SmtExpr elseExpr = translateExpr(expr.right, smtEnv);
    return new SmtIteExpr(condExpr, thenExpr, elseExpr);
  }

  public SmtExpr translateExprConstant(ExprConstant expr, SmtEnv smtEnv)
  {
    switch (expr.op)
    {
      // alloy only supports integers
      case NUMBER:
      {
        SmtExpr intConstant = IntConstant.getSingletonTuple(expr.num);
        return translator.handleIntConstant(intConstant);
      }
      case IDEN:
        return translator.idenAtom.getVariable();
      case TRUE:
        return BoolConstant.True;
      case FALSE:
        return BoolConstant.False;
      default:
        throw new UnsupportedOperationException(expr.op.name());
    }
  }

  SmtExpr translateExprList(ExprList exprList, SmtEnv smtEnv)
  {
    switch (exprList.op)
    {
      case AND:
        return translateExprListAndOr(SmtMultiArityExpr.Op.AND, exprList, smtEnv);
      case OR:
        return translateExprListAndOr(SmtMultiArityExpr.Op.OR, exprList, smtEnv);
      case DISJOINT:
        return translateExprListToDisjBinaryExpressions(SmtMultiArityExpr.Op.DISTINCT, exprList, smtEnv);
      case TOTALORDER:
        throw new UnsupportedOperationException();// total order should be handled before coming here
      default:
        throw new UnsupportedOperationException();
    }
  }

  SmtExpr translateExprListToDisjBinaryExpressions(SmtMultiArityExpr.Op op, ExprList exprList, SmtEnv smtEnv)
  {
    List<SmtExpr> exprs = new ArrayList<>();

    for (Expr e : exprList.args)
    {
      exprs.add(translateExpr(e, smtEnv));
    }
    SmtExpr finalExpr;
    List<SmtExpr> finalExprs = new ArrayList<>();

    if (exprs.size() > 1)
    {
      for (int i = 0; i < exprs.size() - 1; ++i)
      {
        SmtExpr disjExpr = SmtBinaryExpr.Op.EQ.make(translator.atomNone.getVariable(), SmtBinaryExpr.Op.INTERSECTION.make(exprs.get(i), exprs.get(i + 1)));
        finalExprs.add(disjExpr);
      }
      finalExpr = finalExprs.get(0);
      for (int i = 1; i < finalExprs.size(); ++i)
      {
        finalExpr = SmtMultiArityExpr.Op.AND.make(finalExpr, finalExprs.get(i));
      }
    }
    else
    {
      finalExpr = exprs.get(0);
    }
    return finalExpr;
  }

  private SmtExpr translateExprListAndOr(SmtMultiArityExpr.Op op, ExprList exprList, SmtEnv smtEnv)
  {
    if (op != SmtMultiArityExpr.Op.AND && op != SmtMultiArityExpr.Op.OR)
    {
      throw new UnsupportedOperationException(op.toString());
    }

    if (exprList.args.size() == 0)
    {
      if (op == SmtMultiArityExpr.Op.AND)
      {
        return BoolConstant.True;
      }

      if (op == SmtMultiArityExpr.Op.OR)
      {
        return BoolConstant.False;
      }
    }

    List<SmtExpr> smtExprs = new ArrayList<>();

    for (Expr expr : exprList.args)
    {
      SmtExpr smtExpr = translateExpr(expr, smtEnv);
      smtExprs.add(smtExpr);
    }

    return op.make(smtExprs);
  }

  /**
   * Auxiliary functions
   */

  List<SmtVariable> getBdVars(Sort sort, int num)
  {
    List<SmtVariable> bdVars = new ArrayList<>();

    for (int i = 0; i < num; i++)
    {
      bdVars.add(new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false));
    }
    return bdVars;
  }

  List<SmtVariable> getBdTupleVars(List<Sort> sorts, int arity, int num)
  {
    List<Sort> elementSorts = new ArrayList<>();
    List<SmtVariable> bdVars = new ArrayList<>();

    for (int i = 0; i < arity; i++)
    {
      elementSorts.add(sorts.get(i));
    }
    for (int i = 0; i < num; i++)
    {
      Sort sort = new TupleSort(elementSorts);
      bdVars.add(new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false));
    }
    return bdVars;
  }

  SmtExpr mkEmptyRelationOfSort(List<Sort> sorts)
  {
    if (sorts.isEmpty())
    {
      try
      {
        throw new Exception("Unexpected: sorts is empty!");
      }
      catch (Exception ex)
      {
        Logger.getLogger(ExprTranslator.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    return SmtUnaryExpr.Op.EMPTYSET.make(new SetSort(new TupleSort(sorts)));
  }

  SmtExpr mkUnaryRelationOutOfAtomsOrTuples(List<SmtExpr> atomOrTupleExprs)
  {
    List<SmtExpr> atomTupleExprs = new ArrayList<>();

    for (SmtExpr e : atomOrTupleExprs)
    {
      if (e instanceof Variable)
      {
        if (((Variable) e).getDeclaration().getSort() == translator.atomSort ||
            ((Variable) e).getDeclaration().getSort() == translator.uninterpretedInt)
        {
          SmtMultiArityExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, e);
          atomTupleExprs.add(tuple);
        }
        else if (((Variable) e).getDeclaration().getSort() instanceof TupleSort)
        {
          atomTupleExprs.add(e);
        }
        else
        {
          throw new UnsupportedOperationException("Something is wrong here!");
        }
      }
      else
      {
        atomTupleExprs.add(e);
      }
    }


    SmtUnaryExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(atomTupleExprs.get(0));

    if (atomTupleExprs.size() > 1)
    {
      atomTupleExprs.remove(0);
      atomTupleExprs.add(singleton);
      SmtMultiArityExpr set = SmtMultiArityExpr.Op.INSERT.make(atomTupleExprs);
      return set;
    }
    return singleton;
  }

  public SmtExpr solveForVariable(Variable variable, SmtExpr expr, SmtExpr base)
  {
    if (expr.equals(variable))
    {
      return base;
    }
    if (expr instanceof SmtBinaryExpr)
    {
      SmtBinaryExpr binaryExpr = (SmtBinaryExpr) expr;
      switch (binaryExpr.getOp())
      {
        case PRODUCT:
        {
          if (binaryExpr.getA().containsExpr(variable))
          {
            SmtExpr nestedBase = SmtBinaryExpr.Op.JOIN.make(base, binaryExpr.getB());
            SmtExpr solution = solveForVariable(variable, binaryExpr.getA(), nestedBase);
            return  solution;
          }
          if (binaryExpr.getB().containsExpr(variable))
          {
            SmtExpr nestedBase = SmtBinaryExpr.Op.JOIN.make(binaryExpr.getA(), base);
            SmtExpr solution = solveForVariable(variable, binaryExpr.getB(), nestedBase);
            return  solution;
          }
        }
      }
    }
    throw new UnsupportedOperationException();
  }
}
