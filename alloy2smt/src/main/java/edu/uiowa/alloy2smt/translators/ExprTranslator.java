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

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ExprTranslator
{
    final Alloy2SmtTranslator translator;

    final ExprUnaryTranslator exprUnaryTranslator;

    final ExprBinaryTranslator exprBinaryTranslator;

    public ExprTranslator(Alloy2SmtTranslator translator)
    {
        this.translator             = translator;
        this.exprUnaryTranslator    = new ExprUnaryTranslator(this);
        this.exprBinaryTranslator   = new ExprBinaryTranslator(this);
    }

    Expression translateExpr(Expr expr)
    {
        return translateExpr(expr, new HashMap<>());
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
        else if(expr instanceof ExprITE)
        {
            return translateExprITE((ExprITE) expr, variablesScope);
        }
        else if(expr instanceof ExprLet)
        {
            return translateExprLet((ExprLet) expr, variablesScope);
        }  

        throw new UnsupportedOperationException(((ExprCall) expr).toString());
    }
    
    public Expression translateExprITE(ExprITE expr, Map<String,Expression> variablesScope)
    {
        Expression condExpr = translateExpr(expr.cond, variablesScope);
        Expression thenExpr = translateExpr(expr.left, variablesScope);
        Expression elseExpr = translateExpr(expr.right, variablesScope);
        return new ITEExpression(condExpr, thenExpr, elseExpr);
    }

    public Expression translateExprConstant(ExprConstant expr, Map<String,Expression> variablesScope)
    {
        switch (expr.op)
        {
            // alloy only supports integers
            case NUMBER :
            {
                Expression intConstant = IntConstant.getSingletonTuple(expr.num);
                return translator.handleIntConstant(intConstant) ;
            }
            case IDEN   : return translator.atomIden.getVariable();
            case TRUE   : return new BoolConstant(true);
            case FALSE  : return new BoolConstant(false);
            default: throw new UnsupportedOperationException(expr.op.name());
        }
    }   

    Expression translateExprList(ExprList exprList, Map<String, Expression> variablesScope)
    {
        switch (exprList.op)
        {
            case AND        : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, variablesScope);
            case OR         : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, variablesScope);
            case DISJOINT   : return translateExprListToDisjBinaryExpressions(MultiArityExpression.Op.DISTINCT, exprList, variablesScope);
            case TOTALORDER : throw new UnsupportedOperationException();// total order should be handled before coming here
            default         : throw new UnsupportedOperationException();
        }
    }

    Expression translateExprListToDisjBinaryExpressions(MultiArityExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
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
                Expression disjExpr = new BinaryExpression(translator.atomNone.getVariable(), BinaryExpression.Op.EQ, new BinaryExpression(exprs.get(i), BinaryExpression.Op.INTERSECTION, exprs.get(i+1)));
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
        Expression              varExpr         = translateExpr(exprLet.expr, variablesScope);
        Map<String, Expression> varToExprMap    = new HashMap<>();
        String                  sanitizeName    = TranslatorUtils.sanitizeName(exprLet.var.label);
        List<Sort>              exprSorts       = getExprSorts(exprLet.expr);
        Variable varDeclExpr     = new Variable(new ConstantDeclaration(sanitizeName, new SetSort(new TupleSort(exprSorts))));
        
        varToExprMap.put(sanitizeName, varExpr);        
        variablesScope.put(exprLet.var.label, varDeclExpr);
        
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
            return new FunctionCallExpression(translator.getFunctionFromAlloyName(funcName), argExprs);
        }
        else if(this.translator.setComprehensionFuncNameToInputsMap.containsKey(funcName))
        {
            return translateSetComprehensionFuncCallExpr(funcName, argExprs);
        }
        else if(funcName.equals("integer/plus") || funcName.equals("integer/add"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, variablesScope);
        }
        else if(funcName.equals("integer/minus")|| funcName.equals("integer/sub"))
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
        else if(funcName.equals("integer/rem"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MOD, variablesScope);
        }
        else if(translator.functionsMap.containsKey(TranslatorUtils.sanitizeName(funcName)))
        {
            FunctionDeclaration function = translator.getFunction(TranslatorUtils.sanitizeName(funcName));
            return new FunctionCallExpression(function, argExprs);
        }
        else
        {
            FunctionDeclaration function = translator.translateFunction(translator.nameToFuncMap.get(funcName));
            return new FunctionCallExpression(function, argExprs);
        }
    }
    
    public Expression translateSetComprehensionFuncCallExpr(String funcName, List<Expression> argExprs)
    {
        Map<String, Expression> letVars = new HashMap<>();
        List<String> inputs = translator.setComprehensionFuncNameToInputsMap.get(funcName);
        Expression setCompDef = translator.setCompFuncNameToDefMap.get(funcName);
        VariableDeclaration setBdVar = translator.setCompFuncNameToBdVarExprMap.get(funcName);
        
        for(int i = 0; i < argExprs.size(); ++i)
        {
            letVars.put(inputs.get(i), argExprs.get(i));
        }
        
        if(!letVars.isEmpty())
        {
            setCompDef = new LetExpression(LetExpression.Op.LET, letVars, setCompDef);
        }
        if(translator.auxExpr != null)
        {
            translator.auxExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, setCompDef);
        }
        else
        {
            translator.auxExpr = setCompDef;
        }
        translator.existentialBdVars.add(setBdVar);
        return setBdVar.getVariable();
    }
    
    public Expression translateArithmetic(Expression A, Expression B, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {
        if(!translator.arithOps.containsKey(op))
        {                      
            declArithmeticOp(op);
        }
        Expression operation = translator.arithOps.get(op);

        A = convertIntConstantToSet(A);

        B = convertIntConstantToSet(B);

        // for all x, y : uninterpretedInt. x in A and y in B implies
        // exists z :uninterpretedInt. (x, y, z) in operation

        VariableDeclaration x = new VariableDeclaration("_x", Alloy2SmtTranslator.uninterpretedInt);
        VariableDeclaration y = new VariableDeclaration("_y", Alloy2SmtTranslator.uninterpretedInt);
        VariableDeclaration z = new VariableDeclaration("_z", Alloy2SmtTranslator.uninterpretedInt);

        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression xyzTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                x.getVariable(),  y.getVariable(), z.getVariable());

        if(A.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            A = translator.handleIntConstant(A);
        }

        if(B.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            B = translator.handleIntConstant(B);
        }

        Expression xMemberA = new BinaryExpression(xTuple, BinaryExpression.Op.MEMBER, A);
        Expression yMemberB = new BinaryExpression(yTuple, BinaryExpression.Op.MEMBER, B);
        Expression xyzTupleMember = new BinaryExpression(xyzTuple, BinaryExpression.Op.MEMBER, operation);

        Expression and = new BinaryExpression(xMemberA, BinaryExpression.Op.AND, yMemberB);

        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS,
                xyzTupleMember, z);
        Expression implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, exists);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL,
                implies, x, y);
        translator.smtProgram.addAssertion(new Assertion("Operands are in the relation", forAll));

        return new BinaryExpression(B, BinaryExpression.Op.JOIN, new BinaryExpression(A, BinaryExpression.Op.JOIN, operation));
    }

    private Expression convertIntConstantToSet(Expression A)
    {
        if(A instanceof IntConstant)
        {
            ConstantDeclaration uninterpretedInt = translator.getUninterpretedIntConstant((IntConstant) A);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            A = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        }
        return A;
    }

    public void declArithmeticOp(BinaryExpression.Op op)
    {
        VariableDeclaration x = new VariableDeclaration("_x", translator.uninterpretedInt);
        VariableDeclaration y = new VariableDeclaration("_y", translator.uninterpretedInt);
        VariableDeclaration z = new VariableDeclaration("_z", translator.uninterpretedInt);

        Expression xValue = new FunctionCallExpression(translator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(translator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(translator.uninterpretedIntValue, z.getVariable());


        Expression xyzTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                x.getVariable(),  y.getVariable(), z.getVariable());

        String relationName;

        switch(op)
        {
            case PLUS: relationName = Alloy2SmtTranslator.plus; break;
            case MINUS: relationName = Alloy2SmtTranslator.minus; break;
            case MULTIPLY: relationName = Alloy2SmtTranslator.multiply; break;
            case DIVIDE: relationName = Alloy2SmtTranslator.divide; break;
            case MOD: relationName = Alloy2SmtTranslator.mod; break;
            default:
                throw new UnsupportedOperationException(op.toString());
        }

        ConstantDeclaration relation = new ConstantDeclaration(relationName, Alloy2SmtTranslator.setOfTernaryIntSort);
        Expression xyOperation = new BinaryExpression(xValue, op, yValue);
        Expression equal = new BinaryExpression(xyOperation, BinaryExpression.Op.EQ, zValue);
        Expression xyzTupleMember = new BinaryExpression(xyzTuple, BinaryExpression.Op.MEMBER, relation.getVariable());
        Expression implies1 = new BinaryExpression(equal, BinaryExpression.Op.IMPLIES, xyzTupleMember);
        Expression implies2 = new BinaryExpression(xyzTupleMember, BinaryExpression.Op.IMPLIES, equal);
        Expression equivalence = new BinaryExpression(implies1, BinaryExpression.Op.AND, implies2);
        Expression axiom1 = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, equivalence, x, y, z);
        translator.smtProgram.addConstantDeclaration(relation);
        translator.smtProgram.addAssertion(new Assertion(relationName + " relation axiom", axiom1));
        translator.arithOps.put(op, relation.getVariable());

        // the relation is actually a mathematical operation
        // i.e. for all (a,b,c), (x,y,z): (a,b,c) and (x,y,z) in relation and
        // a = x and b = y implies c = z

        VariableDeclaration a = new VariableDeclaration("_a", Alloy2SmtTranslator.uninterpretedInt);
        VariableDeclaration b = new VariableDeclaration("_b", Alloy2SmtTranslator.uninterpretedInt);
        VariableDeclaration c = new VariableDeclaration("_c", Alloy2SmtTranslator.uninterpretedInt);

        Expression abcTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                a.getVariable(),  b.getVariable(), c.getVariable());

        Expression abcTupleMember = new BinaryExpression(abcTuple, BinaryExpression.Op.MEMBER, relation.getVariable());
        Expression axEqual = new BinaryExpression(a.getVariable(), BinaryExpression.Op.EQ, x.getVariable());
        Expression byEqual = new BinaryExpression(b.getVariable(), BinaryExpression.Op.EQ, y.getVariable());
        Expression czEqual = new BinaryExpression(c.getVariable(), BinaryExpression.Op.EQ, z.getVariable());

        Expression and1 = new BinaryExpression(abcTupleMember, BinaryExpression.Op.AND, xyzTupleMember);
        Expression and2 = new BinaryExpression(axEqual, BinaryExpression.Op.AND, byEqual);
        Expression and3 = new BinaryExpression(and1, BinaryExpression.Op.AND, and2);

        Expression implies = new BinaryExpression(and3, BinaryExpression.Op.IMPLIES,czEqual);
        Expression axiom2 = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b, c, x, y , z);
        translator.smtProgram.addAssertion(new Assertion(relationName + " operation axiom", axiom2));
    }

    private Expression translateExprListToBinaryExpressions(BinaryExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
    {

        if(exprList.args.size() == 0 )
        {
            if (op == BinaryExpression.Op.AND)
            {
                return new BoolConstant(true);
            }

            if (op == BinaryExpression.Op.OR)
            {
                return new BoolConstant(false);
            }
            throw new UnsupportedOperationException();
        }

        //ToDo: review the case of nested variable scopes
        Expression left         = translateExpr(exprList.args.get(0), variablesScope);

        if(exprList.args.size() == 1)
        {
            return left;
        }

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
        Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap = new HashMap<>();
        Map<String, Expression> quantifiedVariable2ExpressionMap = new HashMap<>();
        LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap = new LinkedHashMap<>();

        Expression multiplicityConstraint = new BoolConstant(true);
        
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = getDeclarationExpr(decl, variablesScope);
            List<Sort> declSorts    = getExprSorts(decl.expr);

            if( decl.expr instanceof ExprUnary &&
                    ((ExprUnary) decl.expr).op != ExprUnary.Op.ONEOF)
            {
                Sort sort = declSorts.get(0).getSort();
                declSorts = declSorts.stream()
                        .map(s -> new SetSort(new TupleSort(s)))
                        .collect(Collectors.toList());
                for(ExprHasName name : decl.names)
                {
                    VariableDeclaration variable = createVariable(declSorts.get(0), name.label);
                    //ToDo: refactor this for set case
                    quantifiedSingleton2AtomMap.put(name.label, new ArrayList<>(Collections.singletonList(variable)));
                    variablesScope.put(name.label, variable.getVariable());
                    quantifiedVariable2SignatureMap.put(name.label, declExpr);
                    quantifiedVariable2ExpressionMap.put(name.label, variable.getVariable());

                    switch (((ExprUnary) decl.expr).op)
                    {
                        case SOMEOF:
                        {
                            multiplicityConstraint = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ,
                                    new UnaryExpression(UnaryExpression.Op.EMPTYSET, variable.getSort())
                            ));
                        } break;
                        case ONEOF:
                        {
                            VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());
                            quantifiedSingleton2AtomMap.get(name.label).add(multiplicityVariable);
                            multiplicityConstraint = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ,
                                    new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                            new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getVariable()))
                            );
                        } break;
                        case LONEOF:
                        {
                            VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());

                            quantifiedSingleton2AtomMap.get(name.label).add(multiplicityVariable);
                            multiplicityConstraint = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.SUBSET,
                                    new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                            new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getVariable()))
                            );
                        } break;
                    }
                }
            }
            else
            {
                for (ExprHasName name : decl.names)
                {
                    Sort declExprSort = declSorts.get(0);
                    int arity = decl.expr.type().arity();
                    String sanBdVarName = TranslatorUtils.sanitizeName(name.label);

                    VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                    Expression bdVarTupleExpr = bdVarDecl.getVariable();
                    List<VariableDeclaration> bdAtomVars = new ArrayList<>();

                    if (arity > 1) {
                        List<Expression> bdAtomExprs = new ArrayList<>();

                        for (int i = 0; i < arity; i++) {
                            Expression bdAtomVarExpr;
                            String varName = sanBdVarName + "_" + i;
                            VariableDeclaration bdAtomVar;

                            if (declSorts.get(i) instanceof IntSort) {
                                bdAtomVar = new VariableDeclaration(varName, translator.uninterpretedInt);
                                bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getVariable()), 0);
                            } else {
                                bdAtomVar = new VariableDeclaration(varName, translator.atomSort);
                                bdAtomVarExpr = bdAtomVar.getVariable();
                            }
                            bdAtomVars.add(bdAtomVar);
                            bdAtomExprs.add(bdAtomVarExpr);
                        }
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    } else {
                        bdAtomVars.add(bdVarDecl);
                        if ((declExprSort instanceof IntSort)) {
                            bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getVariable());
                        } else {
                            bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                        }
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    }

                    variablesScope.put(name.label, mkSingletonOutOfTuple(bdVarTupleExpr));
                    quantifiedVariable2SignatureMap.put(sanBdVarName, declExpr);
                }
            }
        }
        
        // Translate quantified expression body
        Expression bodyExpr = translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL    : return  translateAllQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case SOME   : return  translateSomeQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case NO     : return  translateNoQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case LONE   : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>(); 
                
                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);
              
                return  translateLoneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                                                quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
            }
            case ONE    : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>(); 
                
                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);
                           
                return  translateOneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                                               quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
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
                VariableDeclaration setBdVar   = new VariableDeclaration(setBdVarName, setSort);
                LinkedHashMap<VariableDeclaration, Expression> bdVars = new LinkedHashMap<>();
                
                for(Decl decl : exprQt.decls)
                {                    
                    Expression declExpr         = getDeclarationExpr(decl, variablesScope);
                    List<Sort> declExprSorts    = getExprSorts(decl.expr);

                    for (ExprHasName name: decl.names)
                    {
                        String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                        VariableDeclaration bdVar = new VariableDeclaration(sanitizedName, declExprSorts.get(0));
                        variablesScope.put(name.label, bdVar.getVariable());
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
                Expression setMembership = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(new ArrayList<>(bdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getVariable());
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
                return setBdVar.getVariable();
            }
            default: throw new UnsupportedOperationException();
        }
    }
    
    private Expression createSndSetBdvarsAndExpr(LinkedHashMap<String, Expression> bdVarToExprMap, 
                                                 Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars,
                                                 Map<String, Expression> bdTupVarNameToTupleExpr, 
                                                 Map<String, Expression> variablesScope, ExprQt exprQt)
    {        
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = getDeclarationExpr(decl, variablesScope);
            List<Sort> declSorts    = getExprSorts(decl.expr);            
            
            for (ExprHasName name: decl.names)
            {
                Sort    declExprSort    = declSorts.get(0);
                int     arity           = decl.expr.type().arity();
                String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                
                VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                Expression bdVarTupleExpr = bdVarDecl.getVariable();
                List<VariableDeclaration>  bdAtomVars    = new ArrayList<>();
                
                if(arity > 1)
                {                                                       
                    List<Expression> bdAtomExprs   = new ArrayList<>();                    
                    for(int i = 0; i < arity; i++)
                    {
                        Expression bdAtomVarExpr;
                        String varName = sanBdVarName+"_"+i+"_2";
                        VariableDeclaration bdAtomVar;
                                                
                        if(declSorts.get(i) instanceof IntSort)
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.uninterpretedInt);
                            bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getVariable()), 0);
                        }
                        else
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.atomSort);
                            bdAtomVarExpr = bdAtomVar.getVariable();
                        } 
                        bdAtomVars.add(bdAtomVar);
                        bdAtomExprs.add(bdAtomVarExpr);
                    }
                    bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);
                }
                else
                {
                    bdAtomVars.add(bdVarDecl);
                    if((declExprSort instanceof IntSort))
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getVariable());
                    }
                    else
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                    }  
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);                    
                }                
                variablesScope.put(name.label, mkSingletonOutOfTuple(bdVarTupleExpr));
                bdVarToExprMap.put(sanBdVarName, declExpr);
            }
        }
        
        // Translate quantified expression body
        return translateExpr(exprQt.sub, variablesScope);        
    }
    
    // (all e: R|not P) or (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateLoneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                               Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                               Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                               Expression bodyExpr, Expression sndBodyExpr, Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P) 
        List<VariableDeclaration> fstBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);
        Expression fstBodyExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        QuantifiedExpression fstQuantExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstBdVars, fstBodyExpr);
        
        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)              
        // all e2 : R
        
        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);
        
        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));
        
        return new BinaryExpression(fstQuantExpr, BinaryExpression.Op.OR, existFormula);
    }   
    
    // (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateOneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                              Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                              Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                              Expression bodyExpr, Expression sndBodyExpr,
                                              Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P) 
        List<VariableDeclaration> fstBdVars = new ArrayList<>();
        
        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);

        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)              
        // all e2 : R
        
        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);
        
        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));
        
        return existFormula;
    }       
    
    private QuantifiedExpression translateNoQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                       Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;     
    }
    
    private Expression getConstraints(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression multiplicityConstraint)
    {
        Expression constraint = new BoolConstant(true);
        
        for(Map.Entry<String, Expression> entry : quantifiedVariable2SignatureMap.entrySet())
        {
            String      name            = entry.getKey();
            Expression  setExpression   = entry.getValue();
            Expression  quantifiedVariableExpression   = quantifiedVariable2ExpressionMap.get(name);

            // add constraint (member (mkTuple x) A) for x: A
            if(quantifiedVariableExpression.getSort() instanceof TupleSort)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.MEMBER, setExpression));
            }
            else // add constraint (subset x A) for x: set A (or lone A, some A)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.SUBSET, setExpression));

            }
        }
        constraint = new BinaryExpression(multiplicityConstraint, BinaryExpression.Op.AND, constraint);
        return constraint;
    }

    private QuantifiedExpression translateAllQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                        Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, bodyExpr);
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;
    }

    private QuantifiedExpression translateSomeQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression bodyExpr, Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, quantifiedVariable2ExpressionMap, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.AND, bodyExpr);
        for(List<VariableDeclaration> vars : quantifiedSingleton2AtomMap.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return quantifiedExpression;
    }


    public BinaryExpression getMemberExpression(Map<VariableDeclaration, Expression> bdVarToExprMap, int index)
    {
        VariableDeclaration bdVar           = (new ArrayList<>(bdVarToExprMap.keySet())).get(index);
        Expression                  bdVarParExpr    = bdVarToExprMap.get(bdVar);
        Expression                  tupleExpr       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVar.getVariable());
        
        if((bdVar.getSort() instanceof UninterpretedSort) || (bdVar.getSort() instanceof IntSort))
        {
            tupleExpr = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVar.getVariable());
        }
        else if(bdVar.getSort() instanceof TupleSort)
        {
            tupleExpr = bdVar.getVariable();
        }
        else if(bdVar.getSort() instanceof SetSort)
        {
            return new BinaryExpression(bdVar.getVariable(), BinaryExpression.Op.SUBSET, bdVarParExpr);
        }
        return new BinaryExpression(tupleExpr, BinaryExpression.Op.MEMBER, bdVarParExpr);
    }

    public Expression getDeclarationExpr(Decl decl, Map<String, Expression> variablesScope)
    {
        return translateExpr(decl.expr, variablesScope);
    }
    
    
    /**
     * Auxiliary functions
     */
        
    List<VariableDeclaration> getBdVars(Sort sort, int num)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort));
        }
        return bdVars;
    }
    
    VariableDeclaration createVariable(Sort sort, String name)
    {
        if(sort instanceof IntSort)
        {
            return new VariableDeclaration(name, translator.uninterpretedInt);
        }
        return new VariableDeclaration(name, sort);
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
                    sorts.add(translator.uninterpretedInt);
                }
                else
                {
                    sorts.add(translator.atomSort);
                }
            }
        }
        return sorts;
    }
    
    List<VariableDeclaration> getBdTupleVars(List<Sort> sorts, int arity, int num)
    {
        List<Sort> elementSorts = new ArrayList<>();
        List<VariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), new TupleSort(elementSorts)));
        }
        return bdVars;
    }    

    Expression mkSingletonOutOfTupleOrAtom(Variable variable)
    {
        UnaryExpression singleton = null;
        
        if((variable.getDeclaration().getSort() instanceof UninterpretedSort) ||
                variable.getDeclaration().getSort() instanceof IntSort)
        {
            MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable);
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);            
        }
        else if(variable.getDeclaration().getSort() instanceof TupleSort)
        {
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, variable);
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
            if(e instanceof Variable)
            {
                if(((Variable)e).getDeclaration().getSort() == translator.atomSort ||
                        ((Variable)e).getDeclaration().getSort() == translator.uninterpretedInt)
                {
                    MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, e);
                    atomTupleExprs.add(tuple);                    
                }
                else if(((Variable)e).getDeclaration().getSort() instanceof TupleSort)
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
