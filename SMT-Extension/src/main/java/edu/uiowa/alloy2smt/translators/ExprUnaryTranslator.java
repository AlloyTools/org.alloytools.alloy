/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.SmtEnv;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

public class ExprUnaryTranslator
{
  final ExprTranslator exprTranslator;
  final Alloy2SmtTranslator translator;
  final ExprVarTranslator exprVarTranslator;

  public ExprUnaryTranslator(ExprTranslator exprTranslator)
  {
    this.exprTranslator = exprTranslator;
    this.translator = exprTranslator.translator;
    this.exprVarTranslator = exprTranslator.exprVarTranslator;
  }

  SmtExpr translateExprUnary(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    switch (exprUnary.op)
    {
      case NOOP:
        return translateNoop(exprUnary, smtEnv);
      case NO:
        return translateNo(exprUnary, smtEnv);
      case SOME:
        return translateSome(exprUnary, smtEnv);
      case ONE:
        return translateOne(exprUnary, smtEnv);
      case ONEOF:
        return translateOneOf(exprUnary, smtEnv);
      case LONEOF:
        return translateLoneOf(exprUnary, smtEnv);
      case SOMEOF:
        return translateSomeOf(exprUnary, smtEnv);
      case SETOF:
        return exprTranslator.translateExpr(exprUnary.sub, smtEnv);
      case LONE:
        return translateLone(exprUnary, smtEnv);
      case CARDINALITY:
        throw new UnsupportedOperationException("CVC4 doesn't support cardinality operator with finite relations!");
      case TRANSPOSE:
        return translateTranspose(exprUnary, smtEnv);
      case CLOSURE:
        return translateClosure(exprUnary, smtEnv);
      case RCLOSURE:
        return translateReflexiveClosure(exprUnary, smtEnv);
      case NOT:
        return translateNot(exprUnary, smtEnv);
      case CAST2INT:
        return translateCAST2INT(exprUnary, smtEnv);
      case CAST2SIGINT:
        return translateCAST2SIGINT(exprUnary, smtEnv);
      default:
      {
        throw new UnsupportedOperationException("Not supported yet: " + exprUnary.op);
      }
    }
  }

  private SmtExpr translateCAST2INT(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    return exprTranslator.translateExpr(exprUnary.sub, smtEnv);
  }

  private SmtExpr translateCAST2SIGINT(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    return exprTranslator.translateExpr(exprUnary.sub, smtEnv);
  }

  private SmtExpr translateNot(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, smtEnv);
    SmtExpr not = SmtUnaryExpr.Op.NOT.make(smtExpr);
    return not;
  }

  private SmtExpr translateClosure(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, smtEnv);
    SmtUnaryExpr closure = SmtUnaryExpr.Op.TCLOSURE.make(smtExpr);
    return closure;
  }

  private SmtExpr translateReflexiveClosure(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtExpr closure = translateClosure(exprUnary, smtEnv);
    SmtBinaryExpr reflexiveClosure;
    if (closure.getSort().equals(AbstractTranslator.setOfBinaryAtomSort))
    {
      reflexiveClosure = SmtBinaryExpr.Op.UNION.make(closure, AbstractTranslator.idenAtom.getVariable());
    }
    else
    {
      reflexiveClosure = SmtBinaryExpr.Op.UNION.make(closure, AbstractTranslator.idenInt.getVariable());
    }
    return reflexiveClosure;
  }

  private SmtExpr translateTranspose(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, smtEnv);
    SmtUnaryExpr transpose = SmtUnaryExpr.Op.TRANSPOSE.make(smtExpr);
    return transpose;
  }


  private SmtExpr translateNoop(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    if (exprUnary.sub instanceof Sig)
    {

      // alloy built in signatures include: univ, none, iden
      if (((Sig) exprUnary.sub).builtin)
      {
        switch (((Sig) exprUnary.sub).label)
        {
          case "univ":
            return Alloy2SmtTranslator.univAtom.getVariable();
          case "iden":
            return Alloy2SmtTranslator.idenAtom.getVariable();
          case "none":
            return Alloy2SmtTranslator.atomNone.getVariable();
          case "Int":
            return Alloy2SmtTranslator.univInt.getVariable();
          default:
            throw new UnsupportedOperationException();
        }
      }
      else
      {
        return translator.signaturesMap.get(((Sig) exprUnary.sub)).getVariable();
      }
    }

    if (exprUnary.sub instanceof Sig.Field)
    {
      return translator.fieldsMap.get(((Sig.Field) exprUnary.sub)).getVariable();
    }

    if (exprUnary.sub instanceof ExprVar)
    {
      return exprVarTranslator.translateExprVar((ExprVar) exprUnary.sub, smtEnv);
    }

    return exprTranslator.translateExpr(exprUnary.sub, smtEnv);
  }

  private SmtExpr translateNo(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtEnv newSmtEnv = new SmtEnv(smtEnv);
    SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newSmtEnv);
    SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
    SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(set, emptySet);
    SmtExpr finalSmtExpr = exprTranslator.addAuxiliaryVariables(isEmpty, newSmtEnv);
    return finalSmtExpr;
  }

  private SmtExpr translateSome(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtEnv newSmtEnv = new SmtEnv(smtEnv);
    SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newSmtEnv);
    SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
    SmtExpr equality = SmtBinaryExpr.Op.EQ.make(set, emptySet);
    SmtExpr isNotEmpty = SmtUnaryExpr.Op.NOT.make(equality);
    SmtExpr finalSmtExpr = exprTranslator.addAuxiliaryVariables(isNotEmpty, newSmtEnv);
    return finalSmtExpr;
  }

  private SmtExpr translateOne(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtEnv newSmtEnv = new SmtEnv(smtEnv);
    SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newSmtEnv);
    Sort sort = ((SetSort) set.getSort()).elementSort;
    SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());
    SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(set, singleton);
    SmtExpr exists = SmtQtExpr.Op.EXISTS.make(isSingleton, variable);
    SmtExpr finalSmtExpr = exprTranslator.addAuxiliaryVariables(exists, newSmtEnv);
    return finalSmtExpr;
  }

  private SmtExpr translateOneOf(ExprUnary expr, SmtEnv smtEnv)
  {
    // expression has pattern (one A) where type of A is (Set E)
    // the translation returns the set (Singleton x) where x satisfies
    // (exists ((x E)) (member x A))

    SmtExpr A = exprTranslator.translateExpr(expr.sub, smtEnv);
    SetSort setSort = (SetSort) A.getSort();
    Sort elementSort = setSort.elementSort;

    SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(elementSort), elementSort, false);

    SmtExpr member = SmtBinaryExpr.Op.MEMBER.make(variable.getVariable(), A);
    variable.setConstraint(member);

    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());

    variable.setConstraint(member);
    smtEnv.addAuxiliaryVariable(variable);
    return singleton;
  }

  private SmtExpr translateLoneOf(ExprUnary expr, SmtEnv smtEnv)
  {
    // expression has pattern (lone A) where type of A is (Set E)
    // the translation returns a set which satisfies
    // (exists ((S (Set E)))
    //      (and
    //          (subset S A)
    //          (exists ((x E)) (subset S (singleton x))) ))

    SmtExpr A = exprTranslator.translateExpr(expr.sub, smtEnv);
    SetSort setSort = (SetSort) A.getSort();
    Sort elementSort = setSort.elementSort;
    SmtVariable setVariable = new SmtVariable(TranslatorUtils.getFreshName(setSort), setSort, false);
    SmtExpr subset1 = SmtBinaryExpr.Op.SUBSET.make(setVariable.getVariable(), A);

    SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(elementSort), elementSort, false);

    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());

    SmtExpr subset2 = SmtBinaryExpr.Op.SUBSET.make(setVariable.getVariable(), singleton);

    SmtQtExpr exists1 = SmtQtExpr.Op.EXISTS.make(subset2, variable);
    SmtExpr andExpr = SmtMultiArityExpr.Op.AND.make(subset1, exists1);
    setVariable.setConstraint(andExpr);
    smtEnv.addAuxiliaryVariable(setVariable);
    return setVariable.getVariable();
  }

  private SmtExpr translateSomeOf(ExprUnary expr, SmtEnv smtEnv)
  {
    // expression has pattern (some A) where type of A is (Set E)
    // the translation returns a set which satisfies
    // (exists ((S (Set E)))
    //      (and
    //          (subset S A)
    //          (not (= S (as emptyset (Set E))))

    SmtExpr A = exprTranslator.translateExpr(expr.sub, smtEnv);
    SetSort setSort = (SetSort) A.getSort();
    SmtVariable setVariable = new SmtVariable(TranslatorUtils.getFreshName(setSort), setSort, false);
    SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(setVariable.getVariable(), A);

    SmtExpr emptyset = SmtUnaryExpr.Op.EMPTYSET.make(setSort);
    SmtExpr equal = SmtBinaryExpr.Op.EQ.make(setVariable.getVariable(), emptyset);
    SmtExpr notEmpty = SmtUnaryExpr.Op.NOT.make(equal);
    SmtExpr andExpr = SmtMultiArityExpr.Op.AND.make(subset, notEmpty);
    setVariable.setConstraint(andExpr);
    smtEnv.addAuxiliaryVariable(setVariable);
    return setVariable.getVariable();
  }

  private SmtExpr translateLone(ExprUnary exprUnary, SmtEnv smtEnv)
  {
    SmtEnv newSmtEnv = new SmtEnv(smtEnv);
    SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newSmtEnv);
    SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
    SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(set, emptySet);
    Sort sort = ((SetSort) set.getSort()).elementSort;
    SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
    SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());
    SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(set, singleton);
    SmtExpr exists = SmtQtExpr.Op.EXISTS.make(isSingleton, variable);
    SmtExpr or = SmtMultiArityExpr.Op.OR.make(isEmpty, exists);
    SmtExpr finalSmtExpr = exprTranslator.addAuxiliaryVariables(or, newSmtEnv);
    return finalSmtExpr;
  }
}
