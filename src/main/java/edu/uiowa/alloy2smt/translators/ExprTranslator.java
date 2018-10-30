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
import java.util.List;
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
        else if(expr instanceof ExprBinary)
        {
            return this.exprBinaryTranslator.translateExprBinary((ExprBinary) expr, variablesScope);
        }
        else if(expr instanceof ExprQt)
        {
            return translateExprQt((ExprQt) expr, variablesScope);
        }
        else if(expr instanceof ExprConstant)
        {
            return translateExprConstant((ExprConstant) expr, variablesScope);
        }
        else if(expr instanceof ExprList)
        {
            return translateExprList((ExprList) expr, variablesScope);
        }
        else if(expr instanceof ExprCall)
        {
            return translateExprCall((ExprCall) expr, variablesScope);
        }        

        throw new UnsupportedOperationException();
    }

    private Expression translateExprConstant(ExprConstant expr, Map<String,ConstantExpression> variablesScope)
    {
        switch (expr.op)
        {
            // alloy only supports integers
            case NUMBER : return new IntConstant(expr.num); 
            case IDEN   : return translator.atomIden.getConstantExpr();
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
            case OR    : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, variablesScope);
            default     : throw new UnsupportedOperationException();
        }
    }
    
    Expression translateExprCall(ExprCall exprCall, Map<String, ConstantExpression> variablesScope)
    {
        String funcName = exprCall.fun.label;
        List<Expression> argExprs = new ArrayList<>();
        
        for(Expr e : exprCall.args)
        {
            argExprs.add(translateExpr(e, variablesScope));
        }
        
        if(funcName.equals("integer/plus"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, variablesScope);
        }
        else if(funcName.equals("integer/minus"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MINUS, variablesScope);
        }
        else if(funcName.equals("integer/mul"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MULTIPLY, variablesScope);
        } 
        else if(funcName.equals("integer/div"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.DIVIDE, variablesScope);
        }         

        throw new UnsupportedOperationException(funcName);
    }    
    
    public Expression translateArithmetic(Expression leftExpr, Expression rightExpr, BinaryExpression.Op op, Map<String,ConstantExpression> variablesScope)
    {
        if(!translator.arithOps.containsKey(op))
        {
            BoundVariableDeclaration  bdIntVar1 = new BoundVariableDeclaration("x", translator.intSort);
            BoundVariableDeclaration  bdIntVar2 = new BoundVariableDeclaration("y", translator.intSort); 
            BoundVariableDeclaration  bdIntVar3 = new BoundVariableDeclaration("z", translator.intSort); 
            Expression memUniv1 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1), BinaryExpression.Op.MEMBER, translator.intUniv);
            Expression memUniv2 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar2), BinaryExpression.Op.MEMBER, translator.intUniv);
            Expression memUniv3 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar3), BinaryExpression.Op.MEMBER, translator.intUniv);            
            ConstantExpression bdIntVar1Expr = new ConstantExpression(bdIntVar1);
            ConstantExpression bdIntVar2Expr = new ConstantExpression(bdIntVar2);
            ConstantExpression bdIntVar3Expr = new ConstantExpression(bdIntVar3);
                       
            Expression lhsExpr = new BinaryExpression(memUniv1, BinaryExpression.Op.AND, memUniv2);
            lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, memUniv3);   
            Expression finalExpr = null;
            Expression rhsExpr  = null;
            ConstantDeclaration arithVarDecl = null;
            
            switch(op)
            {
                case PLUS:     
                    arithVarDecl = new ConstantDeclaration("PLUS", translator.setOfTernaryIntSort);
                    Expression plusExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.PLUS, bdIntVar2Expr);
                    plusExpr = new BinaryExpression(plusExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, plusExpr); 
                    rhsExpr = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);
                    break;
                case MINUS:
                    arithVarDecl = new ConstantDeclaration("MINUS", translator.setOfTernaryIntSort);
                    Expression minusExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MINUS, bdIntVar2Expr);
                    minusExpr = new BinaryExpression(minusExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, minusExpr); 
                    rhsExpr = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);             
                    break;
                case MULTIPLY:
                    arithVarDecl = new ConstantDeclaration("MUL", translator.setOfTernaryIntSort);
                    Expression mulExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MULTIPLY, bdIntVar2Expr);
                    mulExpr = new BinaryExpression(mulExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, mulExpr); 
                    rhsExpr = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);
                  
                    break;
                case DIVIDE:
                    arithVarDecl = new ConstantDeclaration("DIV", translator.setOfTernaryIntSort);
                    Expression divExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.DIVIDE, bdIntVar2Expr);                    
                    divExpr = new BinaryExpression(divExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, divExpr); 
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(bdIntVar2Expr, BinaryExpression.Op.EQ, new IntConstant(0))));
                    rhsExpr = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);                 
                    break;
                default:
                    break;                   
            }
            translator.smtProgram.addConstantDeclaration(arithVarDecl);
            translator.smtProgram.addAssertion(new Assertion(finalExpr));     
            translator.arithOps.put(op, arithVarDecl.getConstantExpr());
        }
        return new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, translator.arithOps.get(op)));
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

        Expression expression = translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL    : return  translateAllQuantifier(boundVariables, expression);
            case SOME   : return  translateSomeQuantifier(boundVariables, expression);
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

    private QuantifiedExpression translateSomeQuantifier(Map<BoundVariableDeclaration, FunctionDeclaration> boundVariables, Expression expression)
    {
        if(boundVariables.size() == 1)
        {
            BinaryExpression member = getMemberExpression(boundVariables, 0);
            expression              = new BinaryExpression(member, BinaryExpression.Op.AND, expression);
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

            expression              = new BinaryExpression(and, BinaryExpression.Op.AND, expression);
        }

        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new ArrayList<>(boundVariables.keySet()), expression);
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
