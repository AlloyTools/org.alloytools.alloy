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

import java.util.Map;

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
            case CARDINALITY: return translateCardinality(exprUnary, variablesScope);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet");
            }
        }
    }


    private Expression translateNoop(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
        if(exprUnary.sub instanceof Sig)
        {
            return exprTranslator.translator.signaturesMap.get(exprUnary.sub).getConstantExpr();
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
            return exprTranslator.translateExprBinary((ExprBinary) exprUnary.sub, variablesScope);
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
        BoundVariableDeclaration    variable    = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        QuantifiedExpression        exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, member, variable);
        return exists;
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

    private Expression translateCardinality(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
       //ToDo: review this case
        TranslatorUtils.generateAuxiliarySetNAtoms(exprTranslator.translator.setOfUnaryAtomSort, 1, exprTranslator.translator);
        throw  new UnsupportedOperationException();
    }
}
