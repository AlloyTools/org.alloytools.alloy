/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
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

    SmtExpr translateExprUnary(ExprUnary exprUnary, Environment environment)
    {
        switch (exprUnary.op)
        {
            case NOOP:
                return translateNoop(exprUnary, environment);
            case NO:
                return translateNo(exprUnary, environment);
            case SOME:
                return translateSome(exprUnary, environment);
            case ONE:
                return translateOne(exprUnary, environment);
            case ONEOF:
                return translateOneOf(exprUnary, environment);
            case LONEOF:
                return translateLoneOf(exprUnary, environment);
            case SOMEOF:
                return exprTranslator.translateExpr(exprUnary.sub, environment);
            case SETOF:
                return exprTranslator.translateExpr(exprUnary.sub, environment);
            case LONE:
                return translateLone(exprUnary, environment);
            case CARDINALITY:
                throw new UnsupportedOperationException("CVC4 doesn't support cardinality operator with finite relations!");
            case TRANSPOSE:
                return translateTranspose(exprUnary, environment);
            case CLOSURE:
                return translateClosure(exprUnary, environment);
            case RCLOSURE:
                return translateReflexiveClosure(exprUnary, environment);
            case NOT:
                return translateNot(exprUnary, environment);
            case CAST2INT:
                return translateCAST2INT(exprUnary, environment);
            case CAST2SIGINT:
                return translateCAST2SIGINT(exprUnary, environment);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet: " + exprUnary.op);
            }
        }
    }

    private SmtExpr translateCAST2INT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }

    private SmtExpr translateCAST2SIGINT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }

    private SmtExpr translateNot(ExprUnary exprUnary, Environment environment)
    {
        SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, environment);
        SmtExpr not = SmtUnaryExpr.Op.NOT.make(smtExpr);
        return not;
    }

    private SmtExpr translateClosure(ExprUnary exprUnary, Environment environment)
    {
        SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, environment);
        SmtUnaryExpr closure = SmtUnaryExpr.Op.TCLOSURE.make(smtExpr);
        return closure;
    }

    private SmtExpr translateReflexiveClosure(ExprUnary exprUnary, Environment environment)
    {
        SmtExpr closure = translateClosure(exprUnary, environment);
        SmtBinaryExpr reflexiveClosure;
        if(closure.getSort().equals(AbstractTranslator.setOfBinaryAtomSort))
        {
            reflexiveClosure = SmtBinaryExpr.Op.UNION.make(closure, AbstractTranslator.idenAtom.getVariable());
        }
        else
        {
            reflexiveClosure = SmtBinaryExpr.Op.UNION.make(closure, AbstractTranslator.idenInt.getVariable());
        }
        return reflexiveClosure;
    }

    private SmtExpr translateTranspose(ExprUnary exprUnary, Environment environment)
    {
        SmtExpr smtExpr = exprTranslator.translateExpr(exprUnary.sub, environment);
        SmtUnaryExpr transpose = SmtUnaryExpr.Op.TRANSPOSE.make(smtExpr);
        return transpose;
    }


    private SmtExpr translateNoop(ExprUnary exprUnary, Environment environment)
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
            return exprVarTranslator.translateExprVar((ExprVar) exprUnary.sub, environment);
        }

        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }

    private SmtExpr translateNo(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
        SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(set, emptySet);
        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(isEmpty, newEnvironment);
        return finalSmtExpr;
    }

    private SmtExpr translateSome(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
        SmtExpr equality = SmtBinaryExpr.Op.EQ.make(set, emptySet);
        SmtExpr isNotEmpty = SmtUnaryExpr.Op.NOT.make(equality);
        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(isNotEmpty, newEnvironment);
        return finalSmtExpr;
    }

    private SmtExpr translateOne(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        Sort sort = ((SetSort) set.getSort()).elementSort;
        SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
        SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());
        SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(set, singleton);
        SmtExpr exists = SmtQtExpr.Op.EXISTS.make(isSingleton, variable);
        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
        return finalSmtExpr;
    }

    private SmtExpr translateOneOf(ExprUnary expr, Environment environment)
    {
        // expression has pattern (one A) where type of A is (Set E)
        // the translation is
        // (exists ((S (Set E)) (x E)) (= S {x}))

        SmtExpr A = exprTranslator.translateExpr(expr.sub, environment);
        SetSort setSort = (SetSort) A.getSort();
        Sort elementSort = setSort.elementSort;
        SmtVariable setVariable = new SmtVariable(TranslatorUtils.getFreshName(setSort), setSort, false);

        SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(elementSort), elementSort, false);

        SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());

        SmtExpr equal = SmtBinaryExpr.Op.EQ.make(setVariable.getVariable(), singleton);
        SmtQtExpr exists = SmtQtExpr.Op.EXISTS.make(equal, setVariable, variable);
        environment.addAuxiliaryFormula(exists);
        return setVariable.getVariable();
    }

    private SmtExpr translateLoneOf(ExprUnary expr, Environment environment)
    {
        // expression has pattern (lone A) where type of A is (Set E)
        // the translation is
        // (exists ((S (Set E)) (x E)) (and (subset S A) (subset S {x})))

        SmtExpr A = exprTranslator.translateExpr(expr.sub, environment);
        SetSort setSort = (SetSort) A.getSort();
        Sort elementSort = setSort.elementSort;
        SmtVariable setVariable = new SmtVariable(TranslatorUtils.getFreshName(setSort), setSort, false);
        SmtExpr subset1 = SmtBinaryExpr.Op.SUBSET.make(setVariable.getVariable(), A);

        SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(elementSort), elementSort, false);

        SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());

        SmtExpr subset2 = SmtBinaryExpr.Op.SUBSET.make(setVariable.getVariable(), singleton);

        SmtExpr andExpr = SmtMultiArityExpr.Op.AND.make(subset1, subset2);
        SmtQtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, setVariable, variable);
        environment.addAuxiliaryFormula(exists);
        return setVariable.getVariable();
    }

    private SmtExpr translateLone(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        SmtExpr set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(set.getSort());
        SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(set, emptySet);
        Sort sort = ((SetSort) set.getSort()).elementSort;
        SmtVariable variable = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
        SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(variable.getVariable());
        SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(set, singleton);
        SmtExpr exists = SmtQtExpr.Op.EXISTS.make(isSingleton, variable);
        SmtExpr or = SmtMultiArityExpr.Op.OR.make(isEmpty, exists);
        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(or, newEnvironment);
        return finalSmtExpr;
    }
}
