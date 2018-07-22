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
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ExprUnaryTranslator
{
    final ExprTranslator exprTranslator;

    public ExprUnaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
    }

    Expression translateExprUnary(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
        switch (exprUnary.op)
        {
            case NOOP       : return translateNoop(exprUnary, variablesScope);
            case NO         : return translateNo(exprUnary, variablesScope);
            case SOME       : return translateSome(exprUnary, variablesScope);
            case ONE        : return translateOne(exprUnary, variablesScope);
            case LONE       : return translateLone(exprUnary, variablesScope);
            case CARDINALITY: throw new UnsupportedOperationException("CVC4 doesn't support cardinality operator with finite relations");
            case TRANSPOSE  : return translateTranspose(exprUnary, variablesScope);
            case CLOSURE    : return translateClosure(exprUnary, variablesScope);
            case RCLOSURE   : return translateReflexiveClosure(exprUnary, variablesScope);
            case NOT        : return translateNot(exprUnary, variablesScope);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet");
            }
        }
    }

    private Expression translateNot(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        Expression expression   = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        Expression not          = new UnaryExpression(UnaryExpression.Op.NOT, expression);
        return not;
    }

    private Expression translateClosure(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        UnaryExpression closure     = new UnaryExpression(UnaryExpression.Op.TCLOSURE, expression);
        return closure;
    }

    private Expression translateReflexiveClosure(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        Expression          closure             = translateClosure(exprUnary, variablesScope);
        BinaryExpression    reflexiveClosure    = new BinaryExpression(closure, BinaryExpression.Op.UNION, exprTranslator.translator.identity.getConstantExpr());
        return reflexiveClosure;
    }

    private Expression translateTranspose(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        UnaryExpression transpose   = new UnaryExpression(UnaryExpression.Op.TRANSPOSE, expression);
        return transpose;
    }


    private Expression translateNoop(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
        if(exprUnary.sub instanceof Sig)
        {
            // alloy built in signatures include: univ, none, iden
            if(((Sig) exprUnary.sub).builtin)
            {
                switch (((Sig) exprUnary.sub).label)
                {
                    case "univ": return exprTranslator.translator.universe;
                    case "iden": return exprTranslator.translator.identity.getConstantExpr();
                    //case "none": return exprTranslator.translator.none;
                    default:
                        throw new UnsupportedOperationException();
                }
            }
            else
            {
                return exprTranslator.translator.signaturesMap.get(exprUnary.sub).getConstantExpr();
            }
        }

        if(exprUnary.sub instanceof Sig.Field)
        {
            return exprTranslator.translator.fieldsMap.get(exprUnary.sub).getConstantExpr();
        }

        if(exprUnary.sub instanceof ExprVar)
        {
            return variablesScope.get(((ExprVar)exprUnary.sub).label);
        }

        if(exprUnary.sub instanceof ExprQt)
        {
            return exprTranslator.translateExprQt((ExprQt) exprUnary.sub, variablesScope);
        }

        if(exprUnary.sub instanceof ExprUnary)
        {
            return translateExprUnary((ExprUnary) exprUnary.sub, variablesScope);
        }

        if(exprUnary.sub instanceof ExprList)
        {
            return exprTranslator.translateExprList((ExprList) exprUnary.sub, variablesScope);
        }

        if(exprUnary.sub instanceof ExprBinary)
        {
            return exprTranslator.exprBinaryTranslator.translateExprBinary((ExprBinary) exprUnary.sub, variablesScope);
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateNo(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
        BoundVariableDeclaration    variable    = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        Expression                  not         = new UnaryExpression(UnaryExpression.Op.NOT, member);
        QuantifiedExpression        forall      = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, not, variable);
        return forall;
    }

    private Expression translateSome(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        List<BoundVariableDeclaration>  variables   = getQuantifiedVariables(exprUnary.sub);
        List<Expression>                expressions = variables.stream().map(v -> v.getConstantExpr()).collect(Collectors.toList());
        MultiArityExpression            tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
        Expression                      set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression                member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        QuantifiedExpression            exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, variables, member);
        return exists;
    }

    private List<BoundVariableDeclaration> getQuantifiedVariables(Expr expr)
    {
        List<BoundVariableDeclaration> variables = new ArrayList<>(expr.type().arity());

        for (int i = 0; i < expr.type().arity() ; i++)
        {
               BoundVariableDeclaration variable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
               variables.add(variable);
        }
        return variables;
    }

    private Expression translateOne(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        BoundVariableDeclaration    existsVar   = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple1      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, existsVar.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member1     = new BinaryExpression(tuple1, BinaryExpression.Op.MEMBER, set);

        BoundVariableDeclaration    forallVar   = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        BinaryExpression            equal       = new BinaryExpression(existsVar.getConstantExpr(), BinaryExpression.Op.EQ, forallVar.getConstantExpr());
        UnaryExpression             notEqual    = new UnaryExpression(UnaryExpression.Op.NOT, equal);

        MultiArityExpression        tuple2      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, forallVar.getConstantExpr());
        BinaryExpression            member2     = new BinaryExpression(tuple2, BinaryExpression.Op.MEMBER, set);
        UnaryExpression             notMember   = new UnaryExpression(UnaryExpression.Op.NOT, member2);

        BinaryExpression            implies1    = new BinaryExpression(notEqual, BinaryExpression.Op.IMPLIES, notMember);
        QuantifiedExpression        forall      = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies1, forallVar);

        BinaryExpression            and         = new BinaryExpression(member1, BinaryExpression.Op.AND, forall);
        QuantifiedExpression        exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and, existsVar);

        return exists;
    }

    private Expression translateLone(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        BoundVariableDeclaration    existsVar   = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple1      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, existsVar.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member1     = new BinaryExpression(tuple1, BinaryExpression.Op.MEMBER, set);

        BoundVariableDeclaration    forallVar   = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        BinaryExpression            equal       = new BinaryExpression(existsVar.getConstantExpr(), BinaryExpression.Op.EQ, forallVar.getConstantExpr());
        UnaryExpression             notEqual    = new UnaryExpression(UnaryExpression.Op.NOT, equal);

        MultiArityExpression        tuple2      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, forallVar.getConstantExpr());
        BinaryExpression            member2     = new BinaryExpression(tuple2, BinaryExpression.Op.MEMBER, set);
        UnaryExpression             notMember   = new UnaryExpression(UnaryExpression.Op.NOT, member2);

        BinaryExpression            implies1    = new BinaryExpression(notEqual, BinaryExpression.Op.IMPLIES, notMember);
        QuantifiedExpression        forall      = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies1, forallVar);

        BinaryExpression            and         = new BinaryExpression(member1, BinaryExpression.Op.AND, forall);
        QuantifiedExpression        exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and, existsVar);


        BoundVariableDeclaration    emptyVar    = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        emptyTuple  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, emptyVar.getConstantExpr());
        BinaryExpression            emptyMember = new BinaryExpression(emptyTuple, BinaryExpression.Op.MEMBER, set);
        UnaryExpression             not         = new UnaryExpression(UnaryExpression.Op.NOT, emptyMember);

        QuantifiedExpression        emptyForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, not, emptyVar);

        BinaryExpression            or          = new BinaryExpression(exists, BinaryExpression.Op.OR, emptyForall);

        return or;
    }
}
