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
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ExprTranslator
{
    final Alloy2SmtTranslator translator;

    final ExprUnaryTranslator exprUnaryTranslator;

    final ExprBinaryTranslator exprBinaryTranslator;

    final ExprQtTranslator exprQtTranslator;

    public ExprTranslator(Alloy2SmtTranslator translator)
    {
        this.translator             = translator;
        this.exprUnaryTranslator    = new ExprUnaryTranslator(this);
        this.exprBinaryTranslator   = new ExprBinaryTranslator(this);
        this.exprQtTranslator       = new ExprQtTranslator(this);
    }

    Expression translateExpr(Expr expr)
    {
        return translateExpr(expr, new Environment());
    }

    Expression translateExpr(Expr expr, Environment environment)
    {
        if(expr instanceof Sig)
        {
            return exprUnaryTranslator.translateExprUnary((ExprUnary)ExprUnary.Op.NOOP.make(null, expr), environment);
        }
        if(expr instanceof ExprUnary)
        {
            return this.exprUnaryTranslator.translateExprUnary((ExprUnary) expr, environment);
        } 
        else if(expr instanceof ExprBinary)
        {
            return this.exprBinaryTranslator.translateExprBinary((ExprBinary) expr, environment);
        }
        else if(expr instanceof ExprQt)
        {
            return exprQtTranslator.translateExprQt((ExprQt) expr, environment);
        }
        else if(expr instanceof ExprConstant)
        {
            return translateExprConstant((ExprConstant) expr, environment);
        }
        else if(expr instanceof ExprList)
        {
            return translateExprList((ExprList) expr, environment);
        }
        else if(expr instanceof ExprCall)
        {
            return translateExprCall((ExprCall) expr, environment);
        }
        else if(expr instanceof ExprITE)
        {
            return translateExprITE((ExprITE) expr, environment);
        }
        else if(expr instanceof ExprLet)
        {
            return translateExprLet((ExprLet) expr, environment);
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
            case NUMBER :
            {
                Expression intConstant = IntConstant.getSingletonTuple(expr.num);
                return translator.handleIntConstant(intConstant) ;
            }
            case IDEN   : return translator.atomIdentity.getVariable();
            case TRUE   : return new BoolConstant(true);
            case FALSE  : return new BoolConstant(false);
            default: throw new UnsupportedOperationException(expr.op.name());
        }
    }   

    Expression translateExprList(ExprList exprList, Environment environment)
    {
        switch (exprList.op)
        {
            case AND        : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, environment);
            case OR         : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, environment);
            case DISJOINT   : return translateExprListToDisjBinaryExpressions(MultiArityExpression.Op.DISTINCT, exprList, environment);
            case TOTALORDER : throw new UnsupportedOperationException();// total order should be handled before coming here
            default         : throw new UnsupportedOperationException();
        }
    }

    Expression translateExprListToDisjBinaryExpressions(MultiArityExpression.Op op, ExprList exprList, Environment environment)
    {        
        List<Expression> exprs = new ArrayList<>();
        
        for(Expr e : exprList.args)
        {
            exprs.add(translateExpr(e, environment));
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
    
    Expression translateExprLet(ExprLet exprLet, Environment environment)
    {
        Expression              varExpr         = translateExpr(exprLet.expr, environment);
        Map<String, Expression> varToExprMap    = new HashMap<>();
        String                  sanitizeName    = TranslatorUtils.sanitizeName(exprLet.var.label);
        Variable varDeclExpr     = new ConstantDeclaration(sanitizeName, varExpr.getSort()).getVariable();
        
        varToExprMap.put(sanitizeName, varExpr);
        // make a new environment
        Environment newEnvironment = new Environment(environment);
        newEnvironment.put(exprLet.var.label, varDeclExpr);
        
        Expression letBodyExpr = translateExpr(exprLet.sub, newEnvironment);
        return new LetExpression(LetExpression.Op.LET, varToExprMap, letBodyExpr);
    }    
    
    Expression translateExprCall(ExprCall exprCall, Environment environment)
    {
        String              funcName = exprCall.fun.label;
        List<Expression>    argExprs = new ArrayList<>();
        
        for(Expr e : exprCall.args)
        {
            argExprs.add(translateExpr(e, environment));
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
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, environment);
        }
        else if(funcName.equals("integer/minus")|| funcName.equals("integer/sub"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MINUS, environment);
        }
        else if(funcName.equals("integer/mul"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MULTIPLY, environment);
        } 
        else if(funcName.equals("integer/div"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.DIVIDE, environment);
        }
        else if(funcName.equals("integer/rem"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MOD, environment);
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
    
    public Expression translateArithmetic(Expression A, Expression B, BinaryExpression.Op op, Environment environment)
    {

        A = convertIntConstantToSet(A);

        B = convertIntConstantToSet(B);

        // for all x, y : uninterpretedInt. x in A and y in B implies
        // exists z :uninterpretedInt. (x, y, z) in operation


        if(A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = translator.handleIntConstant(A);
        }

        if(B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = translator.handleIntConstant(B);
        }

        Expression newA = A;
        Expression newB = B;

        // add variables in the environment as arguments to the result function
        LinkedHashMap<String, Expression> argumentsMap = environment.getVariables();
        List<Sort> argumentSorts = new ArrayList<>();
        List<Expression> arguments = new ArrayList<>();
        List<VariableDeclaration> quantifiedArguments = new ArrayList<>();
        for (Map.Entry<String, Expression> argument: argumentsMap.entrySet())
        {
            arguments.add(argument.getValue());
            Variable variable = (Variable) argument.getValue();
            Sort sort = variable.getSort();
            argumentSorts.add(sort);

            // handle set sorts differently to avoid second order quantification
            if(sort instanceof SetSort)
            {
                Sort elementSort = ((SetSort) sort).elementSort;
                VariableDeclaration tuple = new VariableDeclaration(variable.getName(), elementSort, null);
                tuple.setOriginalName(argument.getKey());
                quantifiedArguments.add(tuple);
                Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple.getVariable());
                newA = newA.replace(argument.getValue(), singleton);
                newB = newB.replace(argument.getValue(), singleton);
                Expression constraint = ((VariableDeclaration)variable.getDeclaration()).getConstraint();
                if(constraint != null)
                {
                    constraint = constraint.replace(variable, singleton);
                }
                tuple.setConstraint(constraint);
            }
            else if (sort instanceof TupleSort || sort instanceof UninterpretedSort)
            {
                quantifiedArguments.add((VariableDeclaration) variable.getDeclaration());
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }

        FunctionDeclaration result = new FunctionDeclaration(TranslatorUtils.getNewSetName(), argumentSorts ,AbstractTranslator.setOfUninterpretedIntTuple);
        translator.smtProgram.addFunction(result);

        Expression resultExpression;
        if(result.getInputSorts().size() > 0)
        {
            resultExpression = new FunctionCallExpression(result, arguments);
        }
        else
        {
            resultExpression = result.getVariable();
        }

        VariableDeclaration x = new VariableDeclaration("__x__", AbstractTranslator.uninterpretedInt, null);
        VariableDeclaration y = new VariableDeclaration("__y__", AbstractTranslator.uninterpretedInt, null);
        VariableDeclaration z = new VariableDeclaration("__z__", AbstractTranslator.uninterpretedInt, null);

        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression zTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getVariable());

        Expression xValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, z.getVariable());

        Expression xMember = new BinaryExpression(xTuple, BinaryExpression.Op.MEMBER, A);
        Expression yMember = new BinaryExpression(yTuple, BinaryExpression.Op.MEMBER, B);
        Expression zMember = new BinaryExpression(zTuple, BinaryExpression.Op.MEMBER, resultExpression);

        Expression xyOperation = new BinaryExpression(xValue, op, yValue);
        Expression equal = new BinaryExpression(xyOperation, BinaryExpression.Op.EQ, zValue);

        Expression and1 = new BinaryExpression(xMember, BinaryExpression.Op.AND, yMember);
        Expression and2 = new BinaryExpression(equal, BinaryExpression.Op.AND, and1);
        Expression exists1 = QuantifiedExpression.Op.EXISTS.make(and2, x, y);
        Expression argumentConstraints = new BoolConstant(true);
        for (VariableDeclaration declaration: quantifiedArguments)
        {
            if(declaration.getConstraint() != null)
            {
                argumentConstraints = new BinaryExpression(argumentConstraints, BinaryExpression.Op.AND, declaration.getConstraint());
            }
        }
        Expression antecedent1 = new BinaryExpression(argumentConstraints, BinaryExpression.Op.AND, zMember);
        Expression implies1 = new BinaryExpression(antecedent1, BinaryExpression.Op.IMPLIES, exists1);
        List<VariableDeclaration> quantifiers1 = new ArrayList<>(quantifiedArguments);
        quantifiers1.add(z);
        Expression forall1 = QuantifiedExpression.Op.FORALL.make(implies1, quantifiers1);

        Assertion assertion1 = new Assertion(String.format("%1$s %2$s %3$s axiom1", op, A, B), forall1);
        translator.smtProgram.addAssertion(assertion1);

        Expression and3 = new BinaryExpression(equal, BinaryExpression.Op.AND,zMember);
        Expression exists2 = QuantifiedExpression.Op.EXISTS.make(and3, z);

        Expression antecedent2 = new BinaryExpression(argumentConstraints, BinaryExpression.Op.AND, and1);

        Expression implies2 = new BinaryExpression(antecedent2, BinaryExpression.Op.IMPLIES, exists2);
        List<VariableDeclaration> quantifiers2 = new ArrayList<>(quantifiedArguments);
        quantifiers2.add(x);
        quantifiers2.add(y);
        Expression forall2 = QuantifiedExpression.Op.FORALL.make(implies2, quantifiers2);

        Assertion assertion2 = new Assertion(String.format("%1$s %2$s %3$s axiom2", op, A, B), forall2);
        translator.smtProgram.addAssertion(assertion2);

        return resultExpression;
    }

    private Expression convertIntConstantToSet(Expression A)
    {
        if(A instanceof IntConstant)
        {
            ConstantDeclaration uninterpretedInt = translator.getUninterpretedIntConstant((IntConstant) A);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            A = UnaryExpression.Op.SINGLETON.make(tuple);
        }
        return A;
    }

    public void declArithmeticOp(BinaryExpression.Op op)
    {
        VariableDeclaration x = new VariableDeclaration("_x", translator.uninterpretedInt, null);
        VariableDeclaration y = new VariableDeclaration("_y", translator.uninterpretedInt, null);
        VariableDeclaration z = new VariableDeclaration("_z", translator.uninterpretedInt, null);

        Expression xValue = new FunctionCallExpression(translator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(translator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(translator.uninterpretedIntValue, z.getVariable());


        Expression xyzTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,
                x.getVariable(),  y.getVariable(), z.getVariable());

        String relationName;

        switch(op)
        {
            case PLUS: relationName = AbstractTranslator.plus; break;
            case MINUS: relationName = AbstractTranslator.minus; break;
            case MULTIPLY: relationName = AbstractTranslator.multiply; break;
            case DIVIDE: relationName = AbstractTranslator.divide; break;
            case MOD: relationName = AbstractTranslator.mod; break;
            default:
                throw new UnsupportedOperationException(op.toString());
        }

        ConstantDeclaration relation = new ConstantDeclaration(relationName, AbstractTranslator.setOfTernaryIntSort);
        Expression xyOperation = new BinaryExpression(xValue, op, yValue);
        Expression equal = new BinaryExpression(xyOperation, BinaryExpression.Op.EQ, zValue);
        Expression xyzTupleMember = new BinaryExpression(xyzTuple, BinaryExpression.Op.MEMBER, relation.getVariable());
        Expression implies1 = new BinaryExpression(equal, BinaryExpression.Op.IMPLIES, xyzTupleMember);
        Expression implies2 = new BinaryExpression(xyzTupleMember, BinaryExpression.Op.IMPLIES, equal);
        Expression equivalence = new BinaryExpression(implies1, BinaryExpression.Op.AND, implies2);
        Expression axiom = QuantifiedExpression.Op.FORALL.make(implies2, x, y, z);
        translator.smtProgram.addConstantDeclaration(relation);
        translator.smtProgram.addAssertion(new Assertion(relationName + " relation axiom", axiom));
        translator.arithmeticOperations.put(op, relation.getVariable());
    }

    private Expression translateExprListToBinaryExpressions(BinaryExpression.Op op, ExprList exprList, Environment environment)
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
        Expression left         = translateExpr(exprList.args.get(0), environment);

        if(exprList.args.size() == 1)
        {
            return left;
        }

        Expression right        = translateExpr(exprList.args.get(1), environment);
        BinaryExpression result = new BinaryExpression(left, op, right);


        for(int i = 2; i < exprList.args.size(); i++)
        {
            Expression expr     = translateExpr(exprList.args.get(i), environment);
            result              = new BinaryExpression(result, op, expr);
        }

        return result;
    }

    /**
     * Auxiliary functions
     */
        
    List<VariableDeclaration> getBdVars(Sort sort, int num)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort, null));
        }
        return bdVars;
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
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), new TupleSort(elementSorts), null));
        }
        return bdVars;
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
        return UnaryExpression.Op.EMPTYSET.make(new SetSort(new TupleSort(sorts)));
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
        
        
        UnaryExpression singleton  = UnaryExpression.Op.SINGLETON.make(atomTupleExprs.get(0));
        
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
