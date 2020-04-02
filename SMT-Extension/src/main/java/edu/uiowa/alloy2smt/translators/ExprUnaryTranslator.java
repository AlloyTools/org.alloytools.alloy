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

import java.util.Collections;

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

    Expression translateExprUnary(ExprUnary exprUnary, Environment environment)
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

    private Expression translateCAST2INT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }

    private Expression translateCAST2SIGINT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }

    private Expression translateNot(ExprUnary exprUnary, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(exprUnary.sub, environment);
        Expression not = UnaryExpression.Op.NOT.make(expression);
        return not;
    }

    private Expression translateClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression closure = UnaryExpression.Op.TCLOSURE.make(expression);
        return closure;
    }

    private Expression translateReflexiveClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression closure = translateClosure(exprUnary, environment);
        BinaryExpression reflexiveClosure;
        if(closure.getSort().equals(AbstractTranslator.setOfBinaryAtomSort))
        {
            reflexiveClosure = BinaryExpression.Op.UNION.make(closure, AbstractTranslator.idenAtom.getVariable());
        }
        else
        {
            reflexiveClosure = BinaryExpression.Op.UNION.make(closure, AbstractTranslator.idenInt.getVariable());
        }
        return reflexiveClosure;
    }

    private Expression translateTranspose(ExprUnary exprUnary, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression transpose = UnaryExpression.Op.TRANSPOSE.make(expression);
        return transpose;
    }


    private Expression translateNoop(ExprUnary exprUnary, Environment environment)
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

    private Expression translateNo(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        Expression set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(set.getSort());
        Expression isEmpty = BinaryExpression.Op.EQ.make(set, emptySet);
        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(isEmpty, newEnvironment);
        return finalExpression;
    }

    private Expression translateSome(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        Expression set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(set.getSort());
        Expression equality = BinaryExpression.Op.EQ.make(set, emptySet);
        Expression isNotEmpty = UnaryExpression.Op.NOT.make(equality);
        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(isNotEmpty, newEnvironment);
        return finalExpression;
    }

    private Expression translateOne(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        Expression set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        Sort sort = ((SetSort) set.getSort()).elementSort;
        VariableDeclaration variable = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
        Expression singleton = UnaryExpression.Op.SINGLETON.make(variable.getVariable());
        Expression isSingleton = BinaryExpression.Op.EQ.make(set, singleton);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(isSingleton, variable);
        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
        return finalExpression;
    }

    private Expression translateOneOf(ExprUnary expr, Environment environment)
    {
        // expression has pattern (one A) where type of A is (Set E)
        // the translation is
        // (exists ((S (Set E)) (x E)) (= S {x}))

        Expression A = exprTranslator.translateExpr(expr.sub, environment);
        SetSort setSort = (SetSort) A.getSort();
        Sort elementSort = setSort.elementSort;
        VariableDeclaration setVariable = new VariableDeclaration(TranslatorUtils.getFreshName(setSort), setSort, false);

        VariableDeclaration variable = new VariableDeclaration(TranslatorUtils.getFreshName(elementSort), elementSort, false);

        Expression singleton = UnaryExpression.Op.SINGLETON.make(variable.getVariable());

        Expression equal = BinaryExpression.Op.EQ.make(setVariable.getVariable(), singleton);
        QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(equal, setVariable, variable);
        environment.addAuxiliaryFormula(exists);
        return setVariable.getVariable();
    }

    private Expression translateLoneOf(ExprUnary expr, Environment environment)
    {
        // expression has pattern (lone A) where type of A is (Set E)
        // the translation is
        // (exists ((S (Set E)) (x E)) (and (subset S A) (subset S {x})))

        Expression A = exprTranslator.translateExpr(expr.sub, environment);
        SetSort setSort = (SetSort) A.getSort();
        Sort elementSort = setSort.elementSort;
        VariableDeclaration setVariable = new VariableDeclaration(TranslatorUtils.getFreshName(setSort), setSort, false);
        Expression subset1 = BinaryExpression.Op.SUBSET.make(setVariable.getVariable(), A);

        VariableDeclaration variable = new VariableDeclaration(TranslatorUtils.getFreshName(elementSort), elementSort, false);

        Expression singleton = UnaryExpression.Op.SINGLETON.make(variable.getVariable());

        Expression subset2 = BinaryExpression.Op.SUBSET.make(setVariable.getVariable(), singleton);

        Expression andExpr = MultiArityExpression.Op.AND.make(subset1, subset2);
        QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(andExpr, setVariable, variable);
        environment.addAuxiliaryFormula(exists);
        return setVariable.getVariable();
    }

    private Expression translateLone(ExprUnary exprUnary, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        Expression set = exprTranslator.translateExpr(exprUnary.sub, newEnvironment);
        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(set.getSort());
        Expression isEmpty = BinaryExpression.Op.EQ.make(set, emptySet);
        Sort sort = ((SetSort) set.getSort()).elementSort;
        VariableDeclaration variable = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
        Expression singleton = UnaryExpression.Op.SINGLETON.make(variable.getVariable());
        Expression isSingleton = BinaryExpression.Op.EQ.make(set, singleton);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(isSingleton, variable);
        Expression or = MultiArityExpression.Op.OR.make(isEmpty, exists);
        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(or, newEnvironment);
        return finalExpression;
    }
}
