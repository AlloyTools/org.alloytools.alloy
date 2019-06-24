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
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ExprUnaryTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;
    public ExprUnaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    Expression translateExprUnary(ExprUnary exprUnary, Environment environment)
    {
        switch (exprUnary.op)
        {
            case NOOP       : return translateNoop(exprUnary, environment);
            case NO         : return translateNo(exprUnary, environment);
            case SOME       : return translateSome(exprUnary, environment);
            case ONE        : return translateOne(exprUnary, environment);
            case ONEOF      : return translateOneOf(exprUnary, environment);
            case LONEOF     : return translateLone(exprUnary, environment);
            case SOMEOF     : return exprTranslator.translateExpr(exprUnary.sub, environment);
            case SETOF      : return exprTranslator.translateExpr(exprUnary.sub, environment);
            case LONE       : return translateLone(exprUnary, environment);
            case CARDINALITY: throw new UnsupportedOperationException("CVC4 doesn't support cardinality operator with finite relations!");
            case TRANSPOSE  : return translateTranspose(exprUnary, environment);
            case CLOSURE    : return translateClosure(exprUnary, environment);
            case RCLOSURE   : return translateReflexiveClosure(exprUnary, environment);
            case NOT        : return translateNot(exprUnary, environment);
            case CAST2INT   : return translateCAST2INT(exprUnary, environment);
            case CAST2SIGINT : return translateCAST2SIGINT(exprUnary, environment);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet: " + exprUnary.op);
            }
        }
    }
    
    private Expression translateCAST2INT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }
    
    private Expression translateCAST2SIGINT(ExprUnary exprUnary, Environment environment)
    {
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }    

    private Expression translateNot(ExprUnary exprUnary, Environment environment)
    {
        Expression expression   = exprTranslator.translateExpr(exprUnary.sub, environment);
        Expression not          = UnaryExpression.Op.NOT.make(expression);
        return not;
    }

    private Expression translateClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression closure     = UnaryExpression.Op.TCLOSURE.make(expression);
        return closure;
    }

    private Expression translateReflexiveClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression          closure             = translateClosure(exprUnary, environment);
        BinaryExpression    reflexiveClosure    = BinaryExpression.Op.UNION.make(closure, AbstractTranslator.atomIdentity.getVariable());
        return reflexiveClosure;
    }

    private Expression translateTranspose(ExprUnary exprUnary, Environment environment)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression transpose   = UnaryExpression.Op.TRANSPOSE.make(expression);
        return transpose;
    }


    private Expression translateNoop(ExprUnary exprUnary, Environment environment)
    {
        if(exprUnary.sub instanceof Sig)
        {

            // alloy built in signatures include: univ, none, iden
            if(((Sig) exprUnary.sub).builtin)
            {
                switch (((Sig) exprUnary.sub).label)
                {                    
                    case "univ": return Alloy2SmtTranslator.atomUniverse.getVariable();
                    case "iden": return Alloy2SmtTranslator.atomIdentity.getVariable();
                    case "none": return Alloy2SmtTranslator.atomNone.getVariable();
                    case "Int":  return Alloy2SmtTranslator.intUniv.getVariable();
                    default:
                        throw new UnsupportedOperationException();
                }
            }
            else
            {
                return translator.signaturesMap.get(((Sig) exprUnary.sub)).getVariable();
            }
        }

        if(exprUnary.sub instanceof Sig.Field)
        {
            return translator.fieldsMap.get(((Sig.Field) exprUnary.sub)).getVariable();
        }

        if(exprUnary.sub instanceof ExprVar)
        {
            String varName = ((ExprVar)exprUnary.sub).label;
            
            if(environment.containsKey(varName))
            {
                Expression constExpr = environment.get(varName);
                
                if(constExpr instanceof Variable)
                {
                    if(((Variable)constExpr).getDeclaration().getSort() == AbstractTranslator.atomSort)
                    {
                        return UnaryExpression.Op.SINGLETON.make(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    }                    
                    else if(((Variable)constExpr).getDeclaration().getSort() == AbstractTranslator.intSort)
                    {
                        return UnaryExpression.Op.SINGLETON.make(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    } 
                    else if(((Variable)constExpr).getDeclaration().getSort() instanceof TupleSort)
                    {
                        return UnaryExpression.Op.SINGLETON.make(constExpr);
                    }                     
                }                
                return constExpr;
            }
            else
            {
                //ToDo: review the semantics of "this" keyword
                if(exprUnary.toString().equals("this"))
                {
                    Sig sig = exprUnary.type().fold().get(0).get(0);
                    return translator.signaturesMap.get(sig).getVariable();
                }
                throw new RuntimeException("Something is wrong: we do not have variable in scope - " + varName);
            }            
        }
        
        return exprTranslator.translateExpr(exprUnary.sub, environment);
    }
    
    private Expression tryAddingExistentialConstraint(Expression expr)
    {
        Expression finalExpr = expr;
        
        if(translator.auxExpr != null)
        {
            finalExpr = BinaryExpression.Op.AND.make(translator.auxExpr, finalExpr);
            finalExpr = QuantifiedExpression.Op.EXISTS.make(finalExpr, translator.existentialBdVars);
            translator.auxExpr = null;
            translator.existentialBdVars.clear();
            
        }
        return finalExpr;
    }


    private Expression translateNo(ExprUnary exprUnary, Environment environment)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = AlloyUtils.getExprSorts(exprUnary.sub);
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, environment);        
        
        List<Sort> elementSorts = new ArrayList<>();

        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        Expression eqExpr = BinaryExpression.Op.EQ.make(set, UnaryExpression.Op.EMPTYSET.make(new SetSort(new TupleSort(elementSorts))));
        return tryAddingExistentialConstraint(eqExpr);
    }

    private Expression translateSome(ExprUnary exprUnary, Environment environment)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = AlloyUtils.getExprSorts(exprUnary.sub);
        Expression someRel  = exprTranslator.translateExpr(exprUnary.sub, environment);  
        List<VariableDeclaration>  bdVars      = new ArrayList<>();
        List<Expression>                bdVarExprs  = new ArrayList<>();        
        
        for(Sort sort : sorts)
        {
            String name = TranslatorUtils.getNewName();
            VariableDeclaration bdVar;
            Expression bdVarExpr;

            bdVar = new VariableDeclaration(name, sort, null);
            bdVarExpr = bdVar.getVariable();

            bdVars.add(bdVar);
            bdVarExprs.add(bdVarExpr);
        }
        Expression bdVarTupExpr     = ExprUnaryTranslator.this.mkOneTupleExprOutofAtoms(bdVarExprs);
        Expression bodyExpr         = BinaryExpression.Op.MEMBER.make(bdVarTupExpr, someRel);
        
        // If the expression is a binary or ternary field, we need to make sure 
        // there exists a var of type binaryIntTup such that the integer tuple equals to the bdVarTupExpr.
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        

        QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(bodyExpr, bdVars);
        return tryAddingExistentialConstraint(exists);
    }    

    private Expression translateOne(ExprUnary exprUnary, Environment environment)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = AlloyUtils.getExprSorts(exprUnary.sub);
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, environment);  
        List<VariableDeclaration>  bdVars      = new ArrayList<>();
        List<Expression>                bdVarExprs  = new ArrayList<>();
        
        for(Sort sort : sorts)
        {
            String name = TranslatorUtils.getNewName();
            VariableDeclaration bdVar;
            Expression bdVarExpr;
            
            if(sort instanceof IntSort)
            {
                bdVar = new VariableDeclaration(name, AbstractTranslator.uninterpretedInt, null);
                bdVarExpr = mkTupleSelExpr(mkUnaryIntTupValue(bdVar.getVariable()), 0);
            }
            else
            {
                bdVar = new VariableDeclaration(name, AbstractTranslator.atomSort, null);
                bdVarExpr = bdVar.getVariable();
            }
            bdVars.add(bdVar);
            bdVarExprs.add(bdVarExpr);
        }
        Expression bdVarTupExpr = mkOneTupleExprOutofAtoms(bdVarExprs);
        Expression bdVarSetExpr = mkSingleton(bdVarTupExpr);
        Expression bodyExpr     = BinaryExpression.Op.EQ.make(bdVarSetExpr, set);
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        
        QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(bodyExpr, bdVars);
        return tryAddingExistentialConstraint(exists);
    }
    
    private Expression translateOneOf(ExprUnary exprUnary, Environment environment)
    {
        Expression set = exprTranslator.translateExpr(exprUnary.sub, environment);

        return set;
    }    

    private Expression translateLone(ExprUnary expr, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(expr.sub, environment);

        if(expr.type().is_bool)
        {
            SetSort sort = (SetSort) expression.getSort();
            Expression emptySet = UnaryExpression.Op.EMPTYSET.make(sort);
            Expression isEmpty = BinaryExpression.Op.EQ.make(emptySet, expression);

            VariableDeclaration element = new VariableDeclaration("__s__", sort.elementSort, null);
            Expression singleton = UnaryExpression.Op.SINGLETON.make(element.getVariable());
            Expression isSingleon = BinaryExpression.Op.EQ.make(singleton, expression);
            Expression exists = QuantifiedExpression.Op.EXISTS.make(isSingleon, element);
            Expression or = BinaryExpression.Op.OR.make(isEmpty, exists);
            return or;
        }
        else
        {
            return expression;
            // (lone e(x, y)) is translated into
            // declare a new set S(x, y)
            // assert forall x, y (x, y constraints) either S(x, y) is singleton or S(x,y) is empty
//            FunctionDeclaration multiplicitySet = translator.multiplicityVariableMap.get(expr);
//
//            if(multiplicitySet != null)
//            {
//                return multiplicitySet.getVariable();
//            }
//            LinkedHashMap<String, Expression> argumentsMap = environment.getVariables();
//            List<VariableDeclaration> quantifiedArguments = new ArrayList<>();
//            List<Expression> arguments = new ArrayList<>();
//            List<Sort> argumentSorts = new ArrayList<>();
//            Expression constraints = BoolConstant.True;
//            for (Map.Entry<String, Expression> argument : argumentsMap.entrySet())
//            {
//                Variable variable = (Variable) argument.getValue();
//
//                VariableDeclaration declaration = (VariableDeclaration) variable.getDeclaration();
//
//                arguments.add(variable);
//                Sort sort = variable.getSort();
//                argumentSorts.add(sort);
//
//                // handle set sorts differently to avoid second order quantification
//                if (sort instanceof SetSort)
//                {
//                    Sort elementSort = ((SetSort) sort).elementSort;
//                    VariableDeclaration tuple = new VariableDeclaration(variable.getName(), elementSort, null);
//                    tuple.setOriginalName(argument.getKey());
//                    quantifiedArguments.add(tuple);
//                    Expression constraint = declaration.getConstraint().replace(variable, tuple.getVariable());
//                    constraints = new BinaryExpression(constraints, BinaryExpression.Op.AND, constraint);
//                }
//                else if (sort instanceof TupleSort || sort instanceof UninterpretedSort)
//                {
//                    quantifiedArguments.add((VariableDeclaration) variable.getDeclaration());
//                    constraints = new BinaryExpression(constraints, BinaryExpression.Op.AND, declaration.getConstraint());
//                }
//                else
//                {
//                    throw new UnsupportedOperationException();
//                }
//            }
//             multiplicitySet = new FunctionDeclaration(TranslatorUtils.getNewSetName(), argumentSorts, expression.getSort());
//
//            translator.smtProgram.addFunction(multiplicitySet);
//            Expression setFunctionExpression;
//
//            if (argumentSorts.size() == 0)
//            {
//                setFunctionExpression = multiplicitySet.getVariable();
//            }
//            else
//            {
//                List<Expression> expressions = AlloyUtils.getFunctionCallArguments(quantifiedArguments, argumentsMap);
//                setFunctionExpression = new FunctionCallExpression(multiplicitySet, expressions);
//            }
//
//            SetSort sort = (SetSort) multiplicitySet.getSort();
//            Expression emptySet = new UnaryExpression(UnaryExpression.Op.EMPTYSET, sort);
//            Expression isEmpty = new BinaryExpression(emptySet, BinaryExpression.Op.EQ, setFunctionExpression);
//
//            VariableDeclaration element = new VariableDeclaration("__s__", sort.elementSort, null);
//            Expression singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, element.getVariable());
//            Expression isSingleon = new BinaryExpression(singleton, BinaryExpression.Op.EQ, setFunctionExpression);
//            Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, isSingleon, element);
//            Expression or = new BinaryExpression(isEmpty, BinaryExpression.Op.OR, exists);
//
//            Expression implies = new BinaryExpression(constraints, BinaryExpression.Op.IMPLIES, or);
//
//            Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, quantifiedArguments, implies);
//
//            Assertion assertion = new Assertion(expr.toString(), forAll);
//            translator.smtProgram.addAssertion(assertion);
//
//            if (argumentSorts.size() == 0)
//            {
//                return multiplicitySet.getVariable();
//            }
//            else
//            {
//                return new FunctionCallExpression(multiplicitySet, arguments);
//            }
        }
    }
    
    public MultiArityExpression mkTupleExpr(VariableDeclaration bdVarDecl)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVarDecl.getVariable());
    }
    
    public MultiArityExpression mkOneTupleExprOutofAtoms(Expression ... exprs)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
    } 
    
    public MultiArityExpression mkOneTupleExprOutofAtoms(List<Expression> exprs)
    {
        return MultiArityExpression.Op.MKTUPLE.make(exprs);
    }
    
    public UnaryExpression mkSingleton(Expression tuple)
    {
        return UnaryExpression.Op.SINGLETON.make(tuple);
    }
    
    public MultiArityExpression mkTupleExpr(List<VariableDeclaration> bdVarDecls)
    {
        List<Expression> constExprs = new ArrayList<>();
        for(VariableDeclaration varDecl : bdVarDecls)
        {
            constExprs.add(varDecl.getVariable());
        }
        return MultiArityExpression.Op.MKTUPLE.make(constExprs);
    }  
    
    public Expression mkTupleSelExpr(Expression expr, int index)
    {
        return BinaryExpression.Op.TUPSEL.make(IntConstant.getInstance(index), expr);
    }
    
    public Expression mkUnaryIntTupValue(Expression expr)
    {
        return new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, expr);
    }
}
