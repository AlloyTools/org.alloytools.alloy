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
import java.util.LinkedHashMap;
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

    Expression translateExpr(Expr expr, Map<String, Expression> variablesScope)
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

    public Expression translateExprConstant(ExprConstant expr, Map<String,Expression> variablesScope)
    {
        switch (expr.op)
        {
            // alloy only supports integers
            case NUMBER : return new IntConstant(expr.num); 
            case IDEN   : return translator.atomIden.getConstantExpr();
            case TRUE   : return new BooleanConstant(true);
            default: throw new UnsupportedOperationException(expr.op.name());
        }
    }


    Expression getSingleton(ConstantExpression constantExpression)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantExpression);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }
    
    Expression getSingletonOutOfAtoms(List<Expression> atomExprs)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }

    Expression getSetOutOfAtoms(List<Expression> atomExprs)
    {
        List<Expression> atomTupleExprs = new ArrayList<>();
        
        for(Expression e : atomExprs)
        {
            MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, e);
            atomTupleExprs.add(tuple);
        }
        
        
        UnaryExpression singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, atomTupleExprs.get(0));
        
        if(atomTupleExprs.size() > 1)
        {
            atomTupleExprs.remove(0);
            atomTupleExprs.add(singleton);
            MultiArityExpression set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atomTupleExprs);            
            return set;
        }
        return singleton;
    }    

    Expression translateExprList(ExprList exprList, Map<String, Expression> variablesScope)
    {
        switch (exprList.op)
        {
            case AND    : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, variablesScope);
            case OR     : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, variablesScope);
            default     : throw new UnsupportedOperationException();
        }
    }
    
    Expression translateExprLet(ExprLet exprLet, Map<String, Expression> variablesScope)
    {
        Expression varExpr = translateExpr(exprLet.expr, variablesScope);
        variablesScope.put(exprLet.var.label, varExpr);
        Expression letBodyExpr = translateExpr(exprLet.sub, variablesScope);
        return letBodyExpr;
    }    
    
    Expression translateExprCall(ExprCall exprCall, Map<String, Expression> variablesScope)
    {
        String              funcName = exprCall.fun.label;
        List<Expression>    argExprs = new ArrayList<>();
        
        for(Expr e : exprCall.args)
        {
            argExprs.add(translateExpr(e, variablesScope));
        }
        
        if(this.translator.funcNamesMap.containsKey(funcName))
        {
            return new FunctionCallExpression(this.translator.funcNamesMap.get(funcName), argExprs);
        }
        else if(funcName.equals("integer/plus"))
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
        else if(!this.translator.funcNamesMap.containsKey(funcName))
        {
            return new FunctionCallExpression(TranslatorUtils.sanitizeName(funcName), argExprs);            
        }
        throw new UnsupportedOperationException(funcName);
    }    
    
    public Expression translateArithmetic(Expression leftExpr, Expression rightExpr, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {
        if(!translator.arithOps.containsKey(op))
        {
            BoundVariableDeclaration  bdIntVar1 = new BoundVariableDeclaration("x", translator.intSort);
            BoundVariableDeclaration  bdIntVar2 = new BoundVariableDeclaration("y", translator.intSort); 
            BoundVariableDeclaration  bdIntVar3 = new BoundVariableDeclaration("z", translator.intSort); 
            Expression memUniv1 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar1), BinaryExpression.Op.MEMBER, translator.intUnivExpr);
            Expression memUniv2 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar2), BinaryExpression.Op.MEMBER, translator.intUnivExpr);
            Expression memUniv3 = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(bdIntVar3), BinaryExpression.Op.MEMBER, translator.intUnivExpr);            
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

    private Expression translateExprListToBinaryExpressions(BinaryExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
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

    Expression translateExprQt(ExprQt exprQt, Map<String, Expression> variablesScope)
    {
        // Get the mapping between bound variables and expressions 
        LinkedHashMap<BoundVariableDeclaration, Expression> bdVarToExprMap = new LinkedHashMap<>();        
        
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr = getDeclarationExpr(decl, variablesScope);
            
            for (ExprHasName name: decl.names)
            {
                int     arity           = decl.expr.type().arity();
                String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                BoundVariableDeclaration bdVarDecl = new BoundVariableDeclaration(sanBdVarName, translator.atomSort);                
                
                if(arity > 1)
                {
                   List<Sort> elementSorts = new ArrayList<>();
                   
                   for(int i = 0; i < arity; i++)
                   {
                       elementSorts.add(translator.atomSort);
                   }
                   bdVarDecl = new BoundVariableDeclaration(sanBdVarName, new TupleSort(elementSorts));
                }

                variablesScope.put(name.label, bdVarDecl.getConstantExpr());
                bdVarToExprMap.put(bdVarDecl, declExpr);
            }
        }
        
        // Translate quantified expression body
        Expression bodyExpr = translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL    : return  translateAllQuantifier(bdVarToExprMap, bodyExpr);
            case SOME   : return  translateSomeQuantifier(bdVarToExprMap, bodyExpr);
            case NO     : return  translateNoQuantifier(bdVarToExprMap, bodyExpr);
            case LONE   : {
                LinkedHashMap<BoundVariableDeclaration, Expression> sndBoundVariables = new LinkedHashMap<>();
                
                for (Decl decl: exprQt.decls)
                {
                    Expression functionDeclaration = getDeclarationExpr(decl, variablesScope);
                    for (ExprHasName name: decl.names)
                    {
                        String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                        String  name2           = sanBdVarName + "_2";
                        int arity = decl.expr.type().arity();
                        BoundVariableDeclaration bdVarDecl = new BoundVariableDeclaration(name2, translator.atomSort);                

                        if(arity > 1)
                        {
                           List<Sort> elementSorts = new ArrayList<>();

                           for(int i = 0; i < arity; i++)
                           {
                               elementSorts.add(translator.atomSort);
                           }
                           bdVarDecl = new BoundVariableDeclaration(name2, new TupleSort(elementSorts));
                        }             
                        // Change the name.label's mapping to a new variable
                        variablesScope.put(name.label, bdVarDecl.getConstantExpr());
                        sndBoundVariables.put(bdVarDecl, functionDeclaration);
                    }
                }   
                Expression expression2 = translateExpr(exprQt.sub, variablesScope);
                return  translateLoneQuantifier(bdVarToExprMap, sndBoundVariables, bodyExpr, expression2);            
            }
            case ONE    : {
                LinkedHashMap<BoundVariableDeclaration, Expression> sndBoundVariables = new LinkedHashMap<>();
                
                for (Decl decl: exprQt.decls)
                {
                    Expression functionDeclaration = getDeclarationExpr(decl, variablesScope);
                    for (ExprHasName name: decl.names)
                    {
                        String name2 = name.label+"_2";
                        int arity = decl.expr.type().arity();
                        BoundVariableDeclaration bdVarDecl = new BoundVariableDeclaration(name2, translator.atomSort);                

                        if(arity > 1)
                        {
                           List<Sort> elementSorts = new ArrayList<>();

                           for(int i = 0; i < arity; i++)
                           {
                               elementSorts.add(translator.atomSort);
                           }
                           bdVarDecl = new BoundVariableDeclaration(name2, new TupleSort(elementSorts));
                        }  
                        // Change the name.label's mapping to a new variable
                        variablesScope.put(name.label, bdVarDecl.getConstantExpr());
                        sndBoundVariables.put(bdVarDecl, functionDeclaration);
                    }
                }   
                Expression expression2 = translateExpr(exprQt.sub, variablesScope);                
                return  translateOneQuantifier(bdVarToExprMap, sndBoundVariables, bodyExpr, expression2);
            }
            case COMPREHENSION :
            {
                //Todo: consider int sort
                List<Sort> elementSorts     = new ArrayList<>();
                
                for(int i = 0; i < exprQt.decls.size(); ++i)
                {                    
                    elementSorts.add(translator.atomSort);
                }
                
                String              setBdVarName    = TranslatorUtils.getNewSetName();
                SetSort             setSort         = new SetSort(new TupleSort(elementSorts));
                BoundVariableDeclaration setBdVar   = new BoundVariableDeclaration(setBdVarName, setSort);
                LinkedHashMap<BoundVariableDeclaration, Expression> bdVars = new LinkedHashMap<>();
                
                for(Decl decl : exprQt.decls)
                {                    
                    Expression declExpr = getDeclarationExpr(decl, variablesScope);

                    for (ExprHasName name: decl.names)
                    {
                        BoundVariableDeclaration bdVar = new BoundVariableDeclaration(name.label, translator.atomSort);
                        variablesScope.put(name.label, bdVar.getConstantExpr());
                        bdVars.put(bdVar, declExpr);
                    }                    
                }
                Expression setCompBodyExpr  = translateExpr(exprQt.sub, variablesScope);
                Expression membership       = getMemberExpression(bdVars, 0);
                
                for(int i = 1; i < bdVars.size(); ++i)
                {
                    membership = new BinaryExpression(membership, BinaryExpression.Op.AND, getMemberExpression(bdVars, i));
                }
                membership = new BinaryExpression(membership, BinaryExpression.Op.AND, setCompBodyExpr);
                Expression setMembership = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(new ArrayList<>(bdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getConstantExpr());
                membership = new BinaryExpression(membership, BinaryExpression.Op.EQ, setMembership);
                Expression forallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(bdVars.keySet()), membership);
                
                if(translator.auxExpr != null)
                {                    
                    translator.auxExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, forallExpr);
                }
                else
                {
                    translator.auxExpr = forallExpr;
                }
                
                translator.existentialBdVars.add(setBdVar);
                return setBdVar.getConstantExpr();
            }
            default: throw new UnsupportedOperationException();
        }
    }
    
    // (all e: R|not P) or (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateLoneQuantifier(LinkedHashMap<BoundVariableDeclaration, Expression> boundVariables, Map<BoundVariableDeclaration, Expression> sndBoundVariables, Expression expression, Expression expression2)
    {
        Expression fstPartBodyExpr = expression;
        Expression sndPartBodyExpr = expression;
        Expression thdPartBodyExpr = expression2;


        BinaryExpression forallMember = getMemberExpression(boundVariables, 0);

        for(int i = 1; i < boundVariables.size(); ++i)
        {
            forallMember = new BinaryExpression(forallMember, BinaryExpression.Op.AND, getMemberExpression(boundVariables, i));
        }
        
        fstPartBodyExpr = new BinaryExpression(forallMember, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fstPartBodyExpr));                
        
        // (all e: R|not P) 
        QuantifiedExpression fstPartQtExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), fstPartBodyExpr);                
        
        // some e : R | P
        sndPartBodyExpr = new BinaryExpression(forallMember, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)              
        // all e2 : R
        BinaryExpression sndForallMemberExpr = getMemberExpression(sndBoundVariables, 0);
        
        for(int i = 1; i < sndBoundVariables.size(); ++i)
        {
            sndForallMemberExpr = new BinaryExpression(sndForallMemberExpr, BinaryExpression.Op.AND, getMemberExpression(sndBoundVariables, i));
        }        
        
        // not(e1 = e2)
        List<BoundVariableDeclaration> fstBdVarDecls = new ArrayList<>();
        List<BoundVariableDeclaration> sndBdVarDecls = new ArrayList<>();        
        
        for(BoundVariableDeclaration bdVarDecl : boundVariables.keySet())
        {
            fstBdVarDecls.add(bdVarDecl);
        }               
        for(BoundVariableDeclaration bdVarDecl : sndBoundVariables.keySet())
        {
            sndBdVarDecls.add(bdVarDecl);
        }        
        
        Expression sndPartDistExpr = TranslatorUtils.mkDistinctExpr(fstBdVarDecls.get(0).getConstantExpr(), sndBdVarDecls.get(0).getConstantExpr());
        
        for(int i = 1; i < fstBdVarDecls.size(); ++i)
        {            
            sndPartDistExpr = new BinaryExpression(sndPartDistExpr, BinaryExpression.Op.AND, 
                                                    TranslatorUtils.mkDistinctExpr(fstBdVarDecls.get(i).getConstantExpr(), sndBdVarDecls.get(i).getConstantExpr()));
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression lastPartExpr = new BinaryExpression(sndForallMemberExpr, BinaryExpression.Op.IMPLIES, 
                                                        new BinaryExpression(sndPartDistExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr)));                
        QuantifiedExpression sndPartQtForallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(sndBoundVariables.keySet()), lastPartExpr);                
        
        sndPartBodyExpr = new BinaryExpression(sndPartBodyExpr, BinaryExpression.Op.AND, sndPartQtForallExpr);
        
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression sndPartQtExistsExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new ArrayList<>(boundVariables.keySet()), sndPartBodyExpr);                
        
        return new BinaryExpression(fstPartQtExpr, BinaryExpression.Op.OR, sndPartQtExistsExpr);      
    }   
    
    private Expression translateOneQuantifier(LinkedHashMap<BoundVariableDeclaration, Expression> boundVariables, Map<BoundVariableDeclaration, Expression> sndBoundVariables, Expression expression, Expression expression2)
    {
        Expression sndPartBodyExpr = expression;
        Expression thdPartBodyExpr = expression2;


        BinaryExpression existsMember = getMemberExpression(boundVariables, 0);

        for(int i = 1; i < boundVariables.size(); ++i)
        {
            existsMember = new BinaryExpression(existsMember, BinaryExpression.Op.AND, getMemberExpression(boundVariables, i));
        }
        
        // some e : R | P
        sndPartBodyExpr = new BinaryExpression(existsMember, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e = e2) => not P)              
        // all e2 : R
        BinaryExpression sndForallMemberExpr = getMemberExpression(sndBoundVariables, 0);
        
        for(int i = 1; i < sndBoundVariables.size(); ++i)
        {
            sndForallMemberExpr = new BinaryExpression(sndForallMemberExpr, BinaryExpression.Op.AND, getMemberExpression(sndBoundVariables, i));
        }        
        
        // not(e1 = e2)
        List<BoundVariableDeclaration> fstBdVarDecls = new ArrayList<>();
        List<BoundVariableDeclaration> sndBdVarDecls = new ArrayList<>();        
        
        for(BoundVariableDeclaration bdVarDecl : boundVariables.keySet())
        {
            fstBdVarDecls.add(bdVarDecl);
        }               
        for(BoundVariableDeclaration bdVarDecl : sndBoundVariables.keySet())
        {
            sndBdVarDecls.add(bdVarDecl);
        }        
        
        Expression sndPartDistExpr = TranslatorUtils.mkDistinctExpr(fstBdVarDecls.get(0).getConstantExpr(), sndBdVarDecls.get(0).getConstantExpr());
        
        for(int i = 1; i < fstBdVarDecls.size(); ++i)
        {            
            sndPartDistExpr = new BinaryExpression(sndPartDistExpr, BinaryExpression.Op.AND, 
                                                    TranslatorUtils.mkDistinctExpr(fstBdVarDecls.get(i).getConstantExpr(), sndBdVarDecls.get(i).getConstantExpr()));
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression lastPartExpr = new BinaryExpression(sndForallMemberExpr, BinaryExpression.Op.IMPLIES, 
                                                        new BinaryExpression(sndPartDistExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr)));                
        QuantifiedExpression sndPartQtForallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(sndBoundVariables.keySet()), lastPartExpr);                
        
        sndPartBodyExpr = new BinaryExpression(sndPartBodyExpr, BinaryExpression.Op.AND, sndPartQtForallExpr);
        
        // (some e : R | P and all e2 : R | not(e = e2) => not P)        
        return new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new ArrayList<>(boundVariables.keySet()), sndPartBodyExpr);
    }       
    
    private QuantifiedExpression translateNoQuantifier(LinkedHashMap<BoundVariableDeclaration, Expression> boundVariables, Expression expression)
    {
        if(boundVariables.size() == 1)
        {
            BinaryExpression member = getMemberExpression(boundVariables, 0);
            expression              = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, expression));
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

            expression              = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, expression));
        }

        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), expression);
        return quantifiedExpression;        
    }

    private QuantifiedExpression translateAllQuantifier(LinkedHashMap<BoundVariableDeclaration, Expression> boundVariables, Expression bodyExpr)
    {
        if(boundVariables.size() == 1)
        {
            BinaryExpression member = getMemberExpression(boundVariables, 0);
            bodyExpr              = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, bodyExpr);
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

            bodyExpr              = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, bodyExpr);
        }

        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), bodyExpr);
        return quantifiedExpression;
    }

    private QuantifiedExpression translateSomeQuantifier(LinkedHashMap<BoundVariableDeclaration, Expression> boundVariables, Expression expression)
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


    public BinaryExpression getMemberExpression(Map<BoundVariableDeclaration, Expression> bdVarToExprMap, int index)
    {
        BoundVariableDeclaration    boundVariable   = (new ArrayList<>(bdVarToExprMap.keySet())).get(index);
        Expression                  bdVarExpr       = bdVarToExprMap.get(boundVariable);
        Expression                  tupleExpr       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, boundVariable.getConstantExpr());
        
        if(boundVariable.getSort() instanceof TupleSort)
        {
            tupleExpr = boundVariable.getConstantExpr();
        }        
        return new BinaryExpression(tupleExpr, BinaryExpression.Op.MEMBER, bdVarExpr);
    }

    private Expression getDeclarationExpr(Decl decl, Map<String, Expression> variablesScope)
    {
        if(decl.expr instanceof ExprUnary)
        {
            Expr expr = (((ExprUnary) decl.expr).sub);
            if(expr instanceof ExprUnary)
            {
                return exprUnaryTranslator.translateExprUnary((ExprUnary)expr, variablesScope);
            } 
            else if(expr instanceof ExprBinary)
            {
                return exprBinaryTranslator.translateExprBinary((ExprBinary)expr, variablesScope);
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
