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
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
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

    public ExprTranslator(Alloy2SmtTranslator translator)
    {
        this.translator = translator;
        this.exprVarTranslator = new ExprVarTranslator(this);
        this.exprUnaryTranslator = new ExprUnaryTranslator(this);
        this.exprBinaryTranslator = new ExprBinaryTranslator(this);
        this.exprQtTranslator = new ExprQtTranslator(this);
        this.exprCallTranslator = new ExprCallTranslator(this);
        this.exprLetTranslator = new ExprLetTranslator(this);
    }

    public Expression translateFormula(String label, Expr expr)
    {
        assert(expr.type() == Type.FORMULA);
        Environment environment = new Environment();
        Expression formula = translateExpr(expr, environment);
        // if there is a multiplicity constraint,
        if(environment.getAuxiliaryFormula() != null)
        {
            QuantifiedExpression quantifiedExpression = environment.getAuxiliaryFormula();
            if(quantifiedExpression.getOp() == QuantifiedExpression.Op.EXISTS)
            {
                Expression body = MultiArityExpression.Op.AND.make(quantifiedExpression.getExpression(), formula);
                formula = QuantifiedExpression.Op.EXISTS.make(body, quantifiedExpression.getVariables());
            }
            else if(quantifiedExpression.getOp() == QuantifiedExpression.Op.FORALL)
            {
                Expression body = BinaryExpression.Op.IMPLIES.make(quantifiedExpression.getExpression(), formula);
                formula = QuantifiedExpression.Op.FORALL.make(body, quantifiedExpression.getVariables());
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }
        Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(expr.pos), label, formula);
        translator.smtProgram.addAssertion(assertion);
        return formula;
    }

    Expression translateExpr(Expr expr, Environment environment)
    {
        if (expr instanceof Sig || expr instanceof Sig.Field)
        {
            //ToDo: refactor this
            return exprUnaryTranslator.translateExprUnary((ExprUnary) ExprUnary.Op.NOOP.make(null, expr), environment);
        }
        if (expr instanceof ExprVar)
        {
            return exprVarTranslator.translateExprVar((ExprVar) expr, environment);
        }
        if (expr instanceof ExprUnary)
        {
            return this.exprUnaryTranslator.translateExprUnary((ExprUnary) expr, environment);
        }
        else if (expr instanceof ExprBinary)
        {
            return this.exprBinaryTranslator.translateExprBinary((ExprBinary) expr, environment);
        }
        else if (expr instanceof ExprQt)
        {
            return exprQtTranslator.translateExprQt((ExprQt) expr, environment);
        }
        else if (expr instanceof ExprConstant)
        {
            return translateExprConstant((ExprConstant) expr, environment);
        }
        else if (expr instanceof ExprList)
        {
            return translateExprList((ExprList) expr, environment);
        }
        else if (expr instanceof ExprCall)
        {
            return exprCallTranslator.translateExprCall((ExprCall) expr, environment);
        }
        else if (expr instanceof ExprITE)
        {
            return translateExprITE((ExprITE) expr, environment);
        }
        else if (expr instanceof ExprLet)
        {
            return exprLetTranslator.translateExprLet((ExprLet) expr, environment);
        }

        throw new UnsupportedOperationException(expr.toString());
    }

    public Expression translateExprITE(ExprITE expr, Environment environment)
    {
        Expression condExpr = translateExpr(expr.cond, environment);
        Expression thenExpr = translateExpr(expr.left, environment);
        Expression elseExpr = translateExpr(expr.right, environment);
        return new ITEExpression(condExpr, thenExpr, elseExpr);
    }

    public Expression translateExprConstant(ExprConstant expr, Environment environment)
    {
        switch (expr.op)
        {
            // alloy only supports integers
            case NUMBER:
            {
                Expression intConstant = IntConstant.getSingletonTuple(expr.num);
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

    Expression translateExprList(ExprList exprList, Environment environment)
    {
        switch (exprList.op)
        {
            case AND:
                return translateExprListAndOr(MultiArityExpression.Op.AND, exprList, environment);
            case OR:
                return translateExprListAndOr(MultiArityExpression.Op.OR, exprList, environment);
            case DISJOINT:
                return translateExprListToDisjBinaryExpressions(MultiArityExpression.Op.DISTINCT, exprList, environment);
            case TOTALORDER:
                throw new UnsupportedOperationException();// total order should be handled before coming here
            default:
                throw new UnsupportedOperationException();
        }
    }

    Expression translateExprListToDisjBinaryExpressions(MultiArityExpression.Op op, ExprList exprList, Environment environment)
    {
        List<Expression> exprs = new ArrayList<>();

        for (Expr e : exprList.args)
        {
            exprs.add(translateExpr(e, environment));
        }
        Expression finalExpr;
        List<Expression> finalExprs = new ArrayList<>();

        if (exprs.size() > 1)
        {
            for (int i = 0; i < exprs.size() - 1; ++i)
            {
                Expression disjExpr = BinaryExpression.Op.EQ.make(translator.atomNone.getVariable(), BinaryExpression.Op.INTERSECTION.make(exprs.get(i), exprs.get(i + 1)));
                finalExprs.add(disjExpr);
            }
            finalExpr = finalExprs.get(0);
            for (int i = 1; i < finalExprs.size(); ++i)
            {
                finalExpr = MultiArityExpression.Op.AND.make(finalExpr, finalExprs.get(i));
            }
        }
        else
        {
            finalExpr = exprs.get(0);
        }
        return finalExpr;
    }

    private Expression translateExprListAndOr(MultiArityExpression.Op op, ExprList exprList, Environment environment)
    {
        if(op != MultiArityExpression.Op.AND && op != MultiArityExpression.Op.OR)
        {
            throw new UnsupportedOperationException(op.toString());
        }

        if (exprList.args.size() == 0)
        {
            if (op == MultiArityExpression.Op.AND)
            {
                return BoolConstant.True;
            }

            if (op == MultiArityExpression.Op.OR)
            {
                return BoolConstant.False;
            }
        }

        List<Expression> expressions = new ArrayList<>();

        for (Expr expr: exprList.args)
        {
            Expression expression = translateExpr(expr, environment);
            expressions.add(expression);
        }

        return op.make(expressions);
    }

    /**
     * Auxiliary functions
     */

    List<VariableDeclaration> getBdVars(Sort sort, int num)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();

        for (int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false));
        }
        return bdVars;
    }

    List<VariableDeclaration> getBdTupleVars(List<Sort> sorts, int arity, int num)
    {
        List<Sort> elementSorts = new ArrayList<>();
        List<VariableDeclaration> bdVars = new ArrayList<>();

        for (int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        for (int i = 0; i < num; i++)
        {
            Sort sort = new TupleSort(elementSorts);
            bdVars.add(new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false));
        }
        return bdVars;
    }

    Expression mkEmptyRelationOfSort(List<Sort> sorts)
    {
        if (sorts.isEmpty())
        {
            try
            {
                throw new Exception("Unexpected: sorts is empty!");
            } catch (Exception ex)
            {
                Logger.getLogger(ExprTranslator.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return UnaryExpression.Op.EMPTYSET.make(new SetSort(new TupleSort(sorts)));
    }

    Expression mkUnaryRelationOutOfAtomsOrTuples(List<Expression> atomOrTupleExprs)
    {
        List<Expression> atomTupleExprs = new ArrayList<>();

        for (Expression e : atomOrTupleExprs)
        {
            if (e instanceof Variable)
            {
                if (((Variable) e).getDeclaration().getSort() == translator.atomSort ||
                        ((Variable) e).getDeclaration().getSort() == translator.uninterpretedInt)
                {
                    MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, e);
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


        UnaryExpression singleton = UnaryExpression.Op.SINGLETON.make(atomTupleExprs.get(0));

        if (atomTupleExprs.size() > 1)
        {
            atomTupleExprs.remove(0);
            atomTupleExprs.add(singleton);
            MultiArityExpression set = MultiArityExpression.Op.INSERT.make(atomTupleExprs);
            return set;
        }
        return singleton;
    }
}
