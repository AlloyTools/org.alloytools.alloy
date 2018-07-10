/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.smtAst.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

public class ExprTranslator
{
    final Alloy2SMTTranslator translator;

    final ExprUnaryTranslator exprUnaryTranslator;

    final ExprBinaryTranslator exprBinaryTranslator;

    public ExprTranslator(Alloy2SMTTranslator translator)
    {
        this.translator             = translator;
        this.exprUnaryTranslator    = new ExprUnaryTranslator(this);
        this.exprBinaryTranslator   = new ExprBinaryTranslator(this);
    }

    Expression translateExpr(Expr expr, Map<String, ConstantExpression> variablesScope)
    {
        if(expr instanceof ExprUnary)
        {
            return this.exprUnaryTranslator.translateExprUnary((ExprUnary) expr, variablesScope);
        }
        if(expr instanceof ExprBinary)
        {
            return this.exprBinaryTranslator.translateExprBinary((ExprBinary) expr, variablesScope);
        }
        if(expr instanceof ExprQt)
        {
            return translateExprQt((ExprQt) expr, variablesScope);
        }

        if(expr instanceof ExprConstant)
        {
            return translateExprConstant((ExprConstant) expr, variablesScope);
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateExprConstant(ExprConstant expr, Map<String,ConstantExpression> variablesScope)
    {
        switch (expr.op)
        {

            case NUMBER: return new IntConstant(expr.num); // allay only  supports integers
                default: throw new UnsupportedOperationException();
        }
    }


    Expression getSingleton(ConstantExpression constantExpression)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantExpression);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }

    Expression translateExprList(ExprList exprList, Map<String, ConstantExpression> variablesScope)
    {
        switch (exprList.op)
        {
            case AND    : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, variablesScope);
            default     : throw new UnsupportedOperationException();
        }
    }

    private Expression translateExprListToBinaryExpressions(BinaryExpression.Op op, ExprList exprList, Map<String, ConstantExpression> variablesScope)
    {
        //ToDo: review the case of nested variable scopes
        Expression left         = translateExpr(exprList.args.get(0), variablesScope);
        Expression right        = translateExpr(exprList.args.get(1), variablesScope);
        BinaryExpression result = new BinaryExpression(left, op, right);


        for(int i = 2; i < exprList.args.size(); i++)
        {
            Expression expr     = translateExpr(exprList.args.get(i), variablesScope);
            //ToDo: review right associativity
            result              = new BinaryExpression(result, op, expr);
        }

        return result;
    }

    Expression translateExprQt(ExprQt exprQt, Map<String, ConstantExpression> variablesScope)
    {
        Map<BoundVariableDeclaration, FunctionDeclaration> boundVariables = new HashMap<>();
        for (Decl decl: exprQt.decls)
        {
            FunctionDeclaration functionDeclaration = getFunctionDeclaration(decl);
            for (ExprHasName name: decl.names)
            {
                BoundVariableDeclaration boundVariable = new BoundVariableDeclaration(name.label, translator.atomSort);
                variablesScope.put(name.label, boundVariable.getConstantExpr());
                boundVariables.put(boundVariable, functionDeclaration);
            }
        }

        Expression           expression             = translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL: return  translateAllQuantifier(boundVariables, expression);
            default: throw new UnsupportedOperationException();
        }
    }

    private QuantifiedExpression translateAllQuantifier(Map<BoundVariableDeclaration, FunctionDeclaration> boundVariables, Expression expression)
    {
        if(boundVariables.size() == 1)
        {
            BinaryExpression member = getMemberExpression(boundVariables, 0);
            expression              = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, expression);
        }
        else if (boundVariables.size() > 1)
        {
            Expression member1 = getMemberExpression(boundVariables, 0);
            Expression member2 = getMemberExpression(boundVariables, 1);

            BinaryExpression and = new BinaryExpression(member1, BinaryExpression.Op.AND, member2);

            for(int i = 2; i < boundVariables.size(); i++)
            {
                Expression member   = getMemberExpression(boundVariables, i);
                and                 = new BinaryExpression(and, BinaryExpression.Op.AND, member);
            }

            expression              = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, expression);
        }

        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), expression);
        return quantifiedExpression;
    }

    private BinaryExpression getMemberExpression(Map<BoundVariableDeclaration, FunctionDeclaration> boundVariables, int index)
    {
        BoundVariableDeclaration    boundVariable       = (new ArrayList<>(boundVariables.keySet())).get(index);
        FunctionDeclaration         functionDeclaration = boundVariables.get(boundVariable);
        MultiArityExpression        tuple               = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, boundVariable.getConstantExpr());
        return new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, functionDeclaration.getConstantExpr());
    }

    private FunctionDeclaration getFunctionDeclaration(Decl decl)
    {
        if(decl.expr instanceof ExprUnary)
        {
            Expr expr = (((ExprUnary) decl.expr).sub);
            if(expr instanceof ExprUnary)
            {
                if(((ExprUnary) expr).sub instanceof Sig)
                {
                    Sig sig = (Sig) ((ExprUnary) expr).sub;
                    return translator.signaturesMap.get(sig);
                }
                else
                {
                    throw new UnsupportedOperationException();
                }
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }
}
