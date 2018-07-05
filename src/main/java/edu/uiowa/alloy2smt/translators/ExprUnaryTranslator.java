package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.Utils;
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
            case NOOP   : return translateNoop(exprUnary, variablesScope);
            case NO     : return translateNo(exprUnary, variablesScope);
            case SOME   : return translateSome(exprUnary, variablesScope);
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

        throw new UnsupportedOperationException();
    }

    private Expression translateNo(ExprUnary exprUnary, Map<String, ConstantExpression> variablesScope)
    {
        BoundVariableDeclaration    variable    = new BoundVariableDeclaration(Utils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        Expression                  expression  = new UnaryExpression(UnaryExpression.Op.NOT, member);
        QuantifiedExpression        forall      = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, expression, variable);
        return forall;
    }

    private Expression translateSome(ExprUnary exprUnary, Map<String,ConstantExpression> variablesScope)
    {
        BoundVariableDeclaration    variable    = new BoundVariableDeclaration(Utils.getNewName(), exprTranslator.translator.atomSort);
        MultiArityExpression        tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable.getConstantExpr());
        Expression                  set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression            member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        QuantifiedExpression        exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, member, variable);
        return exists;
    }
}
