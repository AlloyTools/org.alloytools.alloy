/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.uiowa.alloy2smt.smtAst.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

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
            case FALSE  : return new BooleanConstant(false); 
            default: throw new UnsupportedOperationException(expr.op.name());
        }
    }

    BoundVariableDeclaration getABdAtomVar()
    {
        BoundVariableDeclaration bdVar = new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), translator.atomSort);
        return bdVar;
    }
    
    BoundVariableDeclaration getABdAtomTupleVar(int arity)
    {
        List<Sort> elementSorts = new ArrayList<>();
        
        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(translator.atomSort);
        }
        BoundVariableDeclaration bdVar = new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), new TupleSort(elementSorts));
        return bdVar;
    }    

    Expression translateExprList(ExprList exprList, Map<String, Expression> variablesScope)
    {
        switch (exprList.op)
        {
            case AND        : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, variablesScope);
            case OR         : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, variablesScope);
            case DISJOINT   : return translateExprListToDisjBinaryExpressions(UnaryExpression.Op.DISTINCT, exprList, variablesScope);
            default     : throw new UnsupportedOperationException();
        }
    }
    
    Expression translateExprListToDisjBinaryExpressions(UnaryExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
    {        
        List<Expression> exprs = new ArrayList<>();
        
        for(Expr e : exprList.args)
        {
            exprs.add(translateExpr(e, variablesScope));
        }
        Expression finalExpr;
        List<Expression> finalExprs = new ArrayList<>();
        
        if(exprs.size() > 1)
        {
            for(int i = 0; i < exprs.size()-1; ++i)
            {
                Expression disjExpr = new BinaryExpression(translator.atomNone.getConstantExpr(), BinaryExpression.Op.EQ, new BinaryExpression(exprs.get(i), BinaryExpression.Op.INTERSECTION, exprs.get(i+1)));
                finalExprs.add(disjExpr);
            }
            finalExpr = finalExprs.get(0);
            for(int i = 1; i < finalExprs.size(); ++i)
            {
                finalExpr = new BinaryExpression(finalExpr, BinaryExpression.Op.AND, finalExprs.get(i));
            }
        }
        else
        {
            finalExpr = exprs.get(0);
        }
        return finalExpr;
    }
    
    Expression translateExprLet(ExprLet exprLet, Map<String, Expression> variablesScope)
    {
        Expression varExpr = translateExpr(exprLet.expr, variablesScope);
        Map<String, Expression> varToExprMap = new HashMap<>();
        varToExprMap.put(exprLet.var.label, varExpr);
        Expression letBodyExpr = translateExpr(exprLet.sub, variablesScope);
        return new LetExpression(LetExpression.Op.LET, varToExprMap, letBodyExpr);
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
            BoundVariableDeclaration  bdUnaryIntVar1 = new BoundVariableDeclaration("_x", translator.intAtomSort);
            BoundVariableDeclaration  bdUnaryIntVar2 = new BoundVariableDeclaration("_y", translator.intAtomSort); 
            BoundVariableDeclaration  bdUnaryIntVar3 = new BoundVariableDeclaration("_z", translator.intAtomSort); 
            Expression bdIntVar1Expr = new FunctionCallExpression(translator.valueOfIntAtom.getName(), bdUnaryIntVar1.getConstantExpr());
            Expression bdIntVar2Expr = new FunctionCallExpression(translator.valueOfIntAtom.getName(), bdUnaryIntVar2.getConstantExpr());
            Expression bdIntVar3Expr = new FunctionCallExpression(translator.valueOfIntAtom.getName(), bdUnaryIntVar3.getConstantExpr());
            
            Expression memberOfOp = exprUnaryTranslator.mkTupleExprOutofAtoms(bdIntVar1Expr, bdIntVar2Expr, bdIntVar3Expr);
            
            BoundVariableDeclaration existentialBdVar = new BoundVariableDeclaration("_w", translator.ternaryIntAtomSort);          
            Expression rhsExpr  = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(new FunctionCallExpression(translator.valueOfTernaryIntAtom.getName(), existentialBdVar.getConstantExpr()), 
                                                        BinaryExpression.Op.EQ, memberOfOp), existentialBdVar);
            
            Expression lhsExpr = null;               
            Expression finalExpr = null;
            ConstantDeclaration arithVarDecl = null;
            
            switch(op)
            {
                case PLUS:     
                    arithVarDecl = new ConstantDeclaration("PLUS", translator.setOfTernaryIntSort);
                    lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.PLUS, bdIntVar2Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);

                    rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                    break;
                case MINUS:
                    arithVarDecl = new ConstantDeclaration("MINUS", translator.setOfTernaryIntSort);
                    lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MINUS, bdIntVar2Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);

                    rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);             
                    break;
                case MULTIPLY:
                    arithVarDecl = new ConstantDeclaration("MUL", translator.setOfTernaryIntSort);
                    lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MULTIPLY, bdIntVar2Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);

                    rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                  
                    break;
                case DIVIDE:
                    arithVarDecl = new ConstantDeclaration("DIV", translator.setOfTernaryIntSort);
                    lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.DIVIDE, bdIntVar2Expr);                    
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);

                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(exprUnaryTranslator.mkSingletonOutOfAtomExpr(bdIntVar2Expr), BinaryExpression.Op.EQ, new IntConstant(0))));
                    rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);                 
                    break;
                default:
                    break;                   
            }
            translator.smtProgram.addConstantDeclaration(arithVarDecl);
            translator.smtProgram.addAssertion(new Assertion("Arithmetic operator constant definition", finalExpr));     
            translator.arithOps.put(op, arithVarDecl.getConstantExpr());
        }
        return new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, new BinaryExpression(leftExpr, BinaryExpression.Op.JOIN, translator.arithOps.get(op)));
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
            Expression declExpr     = getDeclarationExpr(decl, variablesScope);
            List<Sort> declSorts    = getExprSorts(decl.expr);            
            
            for (ExprHasName name: decl.names)
            {
                int     arity           = decl.expr.type().arity();
                String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                BoundVariableDeclaration bdVarDecl = getBdVar(declSorts.get(0), sanBdVarName);                
                
                if(arity > 1)
                {
                   bdVarDecl = new BoundVariableDeclaration(sanBdVarName, new TupleSort(declSorts));
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
                LinkedHashMap<BoundVariableDeclaration, Expression> sndBdVarToDeclExprMap = new LinkedHashMap<>();
                
                for (Decl decl: exprQt.decls)
                {
                    Expression declExpr = getDeclarationExpr(decl, variablesScope);
                    
                    for (ExprHasName name: decl.names)
                    {
                        int arity = decl.expr.type().arity();                        
                        String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                        String  name2           = sanBdVarName + "_2";
                        List<Sort> declSorts    = getExprSorts(decl.expr); 
                        
                        BoundVariableDeclaration bdVarDecl = getBdVar(declSorts.get(0), name2);                

                        if(arity > 1)
                        {
                           bdVarDecl = getBdVar(new TupleSort(declSorts), name2);
                        }             
                        // Change the name.label's mapping to a new variable
                        variablesScope.put(name.label, bdVarDecl.getConstantExpr());
                        sndBdVarToDeclExprMap.put(bdVarDecl, declExpr);
                    }
                }   
                Expression expression2 = translateExpr(exprQt.sub, variablesScope);
                return  translateLoneQuantifier(bdVarToExprMap, sndBdVarToDeclExprMap, bodyExpr, expression2);            
            }
            case ONE    : {
                LinkedHashMap<BoundVariableDeclaration, Expression> sndBdVarToExprMap = new LinkedHashMap<>();
                
                for (Decl decl: exprQt.decls)
                {
                    Expression declExpr = getDeclarationExpr(decl, variablesScope);
                    
                    for (ExprHasName name: decl.names)
                    {
                        int arity = decl.expr.type().arity();
                        String sanBdVarName = TranslatorUtils.sanitizeName(name.label);
                        String name2        = sanBdVarName + "_2";                        
                        List<Sort> declSorts    = getExprSorts(decl.expr); 
                        BoundVariableDeclaration bdVarDecl = getBdVar(declSorts.get(0), name2);                

                        if(arity > 1)
                        {
                           bdVarDecl = getBdVar(new TupleSort(declSorts), name2);
                        } 
                        // Change the name.label's mapping to a new variable
                        variablesScope.put(name.label, bdVarDecl.getConstantExpr());
                        sndBdVarToExprMap.put(bdVarDecl, declExpr);
                    }
                }   
                Expression expression2 = translateExpr(exprQt.sub, variablesScope);                
                return  translateOneQuantifier(bdVarToExprMap, sndBdVarToExprMap, bodyExpr, expression2);
            }
            case COMPREHENSION :
            {
                List<Sort> elementSorts     = new ArrayList<>();
                
                for(int i = 0; i < exprQt.decls.size(); ++i)
                {                    
                    for(int j = 0; j < exprQt.decls.get(i).names.size(); ++j)
                    {
                        elementSorts.addAll(getExprSorts(exprQt.decls.get(i).expr));
                    }                    
                }
                
                String              setBdVarName    = TranslatorUtils.getNewSetName();
                SetSort             setSort         = new SetSort(new TupleSort(elementSorts));
                BoundVariableDeclaration setBdVar   = new BoundVariableDeclaration(setBdVarName, setSort);
                LinkedHashMap<BoundVariableDeclaration, Expression> bdVars = new LinkedHashMap<>();
                
                for(Decl decl : exprQt.decls)
                {                    
                    Expression declExpr         = getDeclarationExpr(decl, variablesScope);
                    List<Sort> declExprSorts    = getExprSorts(decl.expr);

                    for (ExprHasName name: decl.names)
                    {
                        BoundVariableDeclaration bdVar = new BoundVariableDeclaration(name.label, declExprSorts.get(0));
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
        
        if((boundVariable.getSort() instanceof UninterpretedSort) || (boundVariable.getSort() instanceof IntSort))
        {
            tupleExpr = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, boundVariable.getConstantExpr());
        }
        else if(boundVariable.getSort() instanceof TupleSort)
        {
            tupleExpr = boundVariable.getConstantExpr();
        }
        else if(boundVariable.getSort() instanceof SetSort)
        {
            return new BinaryExpression(boundVariable.getConstantExpr(), BinaryExpression.Op.SUBSET, bdVarExpr);
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
            else if(expr instanceof Sig.Field)
            {
                return translator.fieldsMap.get((Sig.Field)expr).getConstantExpr();
            }
            else
            {
                throw new UnsupportedOperationException(((ExprBinary)expr).toString());
            }
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }
    
    
    /**
     * Auxiliary functions
     */
    
    
    List<BoundVariableDeclaration> getBdVars(Sort sort, int num)
    {
        List<BoundVariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), sort));
        }
        return bdVars;
    }
    
    BoundVariableDeclaration getBdVar(Sort sort, String name)
    {
        if(sort instanceof IntSort)
        {
            return new BoundVariableDeclaration(name, new TupleSort(sort));
        }
        return new BoundVariableDeclaration(name, sort);
    }    

    List<Sort> getExprSorts(Expr expr)
    {
        List<Sort> sorts = new ArrayList<>();
        for(List<PrimSig> sigs : expr.type().fold())
        {
            for(PrimSig s : sigs)
            {
                if(s.type().is_int())
                {
                    sorts.add(translator.intSort);
                }
                else
                {
                    sorts.add(translator.atomSort);
                }
            }
        }
        return sorts;
    }
    
    List<BoundVariableDeclaration> getBdTupleVars(List<Sort> sorts, int arity, int num)
    {
        List<Sort> elementSorts = new ArrayList<>();
        List<BoundVariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), new TupleSort(elementSorts)));
        }
        return bdVars;
    }    

    Expression mkSingletonOutOfOneAtom(ConstantExpression constantExpression)
    {
        UnaryExpression singleton = null;
        
        if((constantExpression.getDeclaration().getSort() instanceof UninterpretedSort) ||
                constantExpression.getDeclaration().getSort() instanceof IntSort)
        {
            MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantExpression);
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);            
        }
        else if(constantExpression.getDeclaration().getSort() instanceof TupleSort)
        {
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, constantExpression);  
        }
        else
        {
            throw new UnsupportedOperationException("Unexpected!");
        }
        return singleton;
    }
    
    
    
    Expression mkSingletonOutOfAtoms(List<Expression> atomExprs)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }
    
    Expression mkSingletonOutOfTuple(Expression tupleExpr)
    {
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tupleExpr);
        return singleton;
    }    
    
    Expression mkEmptyRelationOfSort(List<Sort> sorts) 
    {
        if(sorts.isEmpty())
        {
            try {
                throw new Exception("Unexpected: sorts is empty!");
            } catch (Exception ex) {
                Logger.getLogger(ExprTranslator.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, new SetSort(new TupleSort(sorts)));
    }

    Expression mkUnaryRelationOutOfAtomsOrTuples(List<Expression> atomOrTupleExprs)
    {
        List<Expression> atomTupleExprs = new ArrayList<>();
        
        for(Expression e : atomOrTupleExprs)
        {
            if(e instanceof ConstantExpression)
            {
                if(((ConstantExpression)e).getDeclaration().getSort() == translator.atomSort || 
                        ((ConstantExpression)e).getDeclaration().getSort() == translator.intSort)
                {
                    MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, e);
                    atomTupleExprs.add(tuple);                    
                }
                else if(((ConstantExpression)e).getDeclaration().getSort() instanceof TupleSort)
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
}
