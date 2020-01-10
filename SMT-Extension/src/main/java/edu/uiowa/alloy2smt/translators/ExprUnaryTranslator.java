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
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;

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
        BinaryExpression reflexiveClosure = BinaryExpression.Op.UNION.make(closure, AbstractTranslator.idenAtom.getVariable());
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

    private Expression tryAddingExistentialConstraint(Expression expr)
    {
        Expression finalExpr = expr;

        if (translator.auxExpr != null)
        {
            finalExpr = MultiArityExpression.Op.AND.make(translator.auxExpr, finalExpr);
            finalExpr = QuantifiedExpression.Op.EXISTS.make(finalExpr, translator.existentialBdVars);
            translator.auxExpr = null;
            translator.existentialBdVars.clear();

        }
        return finalExpr;
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

    private Expression translateOneOf(ExprUnary exprUnary, Environment environment)
    {
        Expression set = exprTranslator.translateExpr(exprUnary.sub, environment);

        return set;
    }

    private Expression translateLoneOf(ExprUnary exprUnary, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(exprUnary.sub, environment);
        return expression;
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

    public MultiArityExpression mkTupleExpr(VariableDeclaration bdVarDecl)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVarDecl.getVariable());
    }

    public MultiArityExpression mkOneTupleExprOutofAtoms(Expression... exprs)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
    }

    public MultiArityExpression mkOneTupleExprOutofAtoms(List<Expression> exprs)
    {
        return MultiArityExpression.Op.MKTUPLE.make(exprs);
    }

    public UnaryExpression mkSingleton(Expression tuple)
    {
        return UnaryExpression.Op.SINGLETON.make(tuple);
    }

    public MultiArityExpression mkTupleExpr(List<VariableDeclaration> bdVarDecls)
    {
        List<Expression> constExprs = new ArrayList<>();
        for (VariableDeclaration varDecl : bdVarDecls)
        {
            constExprs.add(varDecl.getVariable());
        }
        return MultiArityExpression.Op.MKTUPLE.make(constExprs);
    }

    public Expression mkTupleSelExpr(Expression expr, int index)
    {
        return BinaryExpression.Op.TUPSEL.make(IntConstant.getInstance(index), expr);
    }

    public Expression mkUnaryIntTupValue(Expression expr)
    {
        return new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, expr);
    }
}
