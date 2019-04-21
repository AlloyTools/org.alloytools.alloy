/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class ExprUnaryTranslator
{
    final ExprTranslator exprTranslator;
    final String valueOfUnaryIntTup;

    public ExprUnaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator         = exprTranslator;
        this.valueOfUnaryIntTup     = getTranslator().uninterpretedIntValue.getName();
    }

    Expression translateExprUnary(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        switch (exprUnary.op)
        {
            case NOOP       : return translateNoop(exprUnary, variablesScope);
            case NO         : return translateNo(exprUnary, variablesScope);
            case SOME       : return translateSome(exprUnary, variablesScope);
            case ONE        : return translateOne(exprUnary, variablesScope);
            case ONEOF      : return translateOneOf(exprUnary, variablesScope);
            case LONEOF     : return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
            case SOMEOF     : return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
            case SETOF      : return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
            case LONE       : return translateLone(exprUnary, variablesScope);
            case CARDINALITY: throw new UnsupportedOperationException("CVC4 doesn't support cardinality operator with finite relations!");
            case TRANSPOSE  : return translateTranspose(exprUnary, variablesScope);
            case CLOSURE    : return translateClosure(exprUnary, variablesScope);
            case RCLOSURE   : return translateReflexiveClosure(exprUnary, variablesScope);
            case NOT        : return translateNot(exprUnary, variablesScope);
            case CAST2INT   : return translateCAST2INT(exprUnary, variablesScope);
            case CAST2SIGINT : return translateCAST2SIGINT(exprUnary, variablesScope);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet: " + exprUnary.op);
            }
        }
    }
    
    private Expression translateCAST2INT(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
    }
    
    private Expression translateCAST2SIGINT(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
    }    

    private Expression translateNot(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        Expression expression   = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        Expression not          = new UnaryExpression(UnaryExpression.Op.NOT, expression);
        return not;
    }

    private Expression translateClosure(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        UnaryExpression closure     = new UnaryExpression(UnaryExpression.Op.TCLOSURE, expression);
        return closure;
    }

    private Expression translateReflexiveClosure(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        Expression          closure             = translateClosure(exprUnary, variablesScope);
        BinaryExpression    reflexiveClosure    = new BinaryExpression(closure, BinaryExpression.Op.UNION, getTranslator().atomIdentity.getVariable());
        return reflexiveClosure;
    }

    private Expression translateTranspose(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        UnaryExpression transpose   = new UnaryExpression(UnaryExpression.Op.TRANSPOSE, expression);
        return transpose;
    }


    private Expression translateNoop(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        if(exprUnary.sub instanceof Sig)
        {

            // alloy built in signatures include: univ, none, iden
            if(((Sig) exprUnary.sub).builtin)
            {
                switch (((Sig) exprUnary.sub).label)
                {                    
                    case "univ": return getTranslator().atomUniverse.getVariable();
                    case "iden": return getTranslator().atomIdentity.getVariable();
                    case "none": return getTranslator().atomNone.getVariable();
                    case "Int": throw new UnsupportedOperationException("We do not support the built-in signature Int used in facts!");
                    default:
                        throw new UnsupportedOperationException();
                }
            }
            else
            {
                return getTranslator().signaturesMap.get(((Sig) exprUnary.sub)).getVariable();
            }
        }

        if(exprUnary.sub instanceof Sig.Field)
        {
            return getTranslator().fieldsMap.get(((Sig.Field) exprUnary.sub)).getVariable();
        }

        if(exprUnary.sub instanceof ExprVar)
        {
            String varName = ((ExprVar)exprUnary.sub).label;
            
            if(variablesScope.containsKey(varName))
            {
                Expression constExpr = variablesScope.get(varName);
                
                if(constExpr instanceof Variable)
                {
                    if(((Variable)constExpr).getDeclaration().getSort() == getTranslator().atomSort)
                    {
                        return new UnaryExpression(UnaryExpression.Op.SINGLETON, new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    }                    
                    else if(((Variable)constExpr).getDeclaration().getSort() == getTranslator().intSort)
                    {
                        return new UnaryExpression(UnaryExpression.Op.SINGLETON, new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    } 
                    else if(((Variable)constExpr).getDeclaration().getSort() instanceof TupleSort)
                    {
                        return new UnaryExpression(UnaryExpression.Op.SINGLETON, constExpr);
                    }                     
                }                
                return constExpr;
            }
            else
            {
                throw new RuntimeException("Something is wrong: we do not have variable in scope - " + varName);
            }            
        }
        
        return exprTranslator.translateExpr(exprUnary.sub, variablesScope);
    }
    
    private Expression tryAddingExistentialConstraint(Expression expr)
    {
        Expression finalExpr = expr;
        
        if(getTranslator().auxExpr != null)
        {
            finalExpr = new BinaryExpression(getTranslator().auxExpr, BinaryExpression.Op.AND, finalExpr);            
            finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, getTranslator().existentialBdVars, finalExpr);
            getTranslator().auxExpr = null;
            getTranslator().existentialBdVars.clear();            
            
        }
        return finalExpr;
    }


    private Expression translateNo(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = exprTranslator.getExprSorts(exprUnary.sub);
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, variablesScope);        
        
        List<Sort> elementSorts = new ArrayList<>();

        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        Expression eqExpr = new BinaryExpression(set, BinaryExpression.Op.EQ, 
                                    new UnaryExpression(UnaryExpression.Op.EMPTYSET, new SetSort(new TupleSort(elementSorts))));         
        return tryAddingExistentialConstraint(eqExpr);
    }

    private Expression translateSome(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = exprTranslator.getExprSorts(exprUnary.sub);
        Expression someRel  = exprTranslator.translateExpr(exprUnary.sub, variablesScope);  
        List<VariableDeclaration>  bdVars      = new ArrayList<>();
        List<Expression>                bdVarExprs  = new ArrayList<>();        
        
        for(Sort sort : sorts)
        {
            String name = TranslatorUtils.getNewName();
            VariableDeclaration bdVar;
            Expression bdVarExpr;
            
            if(sort instanceof IntSort)
            {
                bdVar = new VariableDeclaration(name, getTranslator().uninterpretedInt);
                bdVarExpr = mkTupleSelExpr(mkUnaryIntTupValue(bdVar.getVariable()), 0);
            }
            else
            {
                bdVar = new VariableDeclaration(name, getTranslator().atomSort);
                bdVarExpr = bdVar.getVariable();
            }
            bdVars.add(bdVar);
            bdVarExprs.add(bdVarExpr);
        }
        Expression bdVarTupExpr     = ExprUnaryTranslator.this.mkOneTupleExprOutofAtoms(bdVarExprs);
        Expression bodyExpr         = new BinaryExpression(bdVarTupExpr, BinaryExpression.Op.MEMBER, someRel);
        
        // If the expression is a binary or ternary field, we need to make sure 
        // there exists a var of type binaryIntTup such that the integer tuple equals to the bdVarTupExpr.
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        

        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return tryAddingExistentialConstraint(exists);
    }    

    private Expression translateOne(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = exprTranslator.getExprSorts(exprUnary.sub);
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, variablesScope);  
        List<VariableDeclaration>  bdVars      = new ArrayList<>();
        List<Expression>                bdVarExprs  = new ArrayList<>();
        
        for(Sort sort : sorts)
        {
            String name = TranslatorUtils.getNewName();
            VariableDeclaration bdVar;
            Expression bdVarExpr;
            
            if(sort instanceof IntSort)
            {
                bdVar = new VariableDeclaration(name, getTranslator().uninterpretedInt);
                bdVarExpr = mkTupleSelExpr(mkUnaryIntTupValue(bdVar.getVariable()), 0);
            }
            else
            {
                bdVar = new VariableDeclaration(name, getTranslator().atomSort);
                bdVarExpr = bdVar.getVariable();
            }
            bdVars.add(bdVar);
            bdVarExprs.add(bdVarExpr);
        }
        Expression bdVarTupExpr = mkOneTupleExprOutofAtoms(bdVarExprs);
        Expression bdVarSetExpr = mkSingleton(bdVarTupExpr);
        Expression bodyExpr     = new BinaryExpression(bdVarSetExpr, BinaryExpression.Op.EQ, set);
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        
        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return tryAddingExistentialConstraint(exists);
    }
    
    private Expression translateOneOf(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        Expression set = exprTranslator.translateExpr(exprUnary.sub, variablesScope);

        return set;
    }    

    private Expression translateLone(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        int arity           = exprUnary.sub.type().arity();
        List<Sort> sorts    = exprTranslator.getExprSorts(exprUnary.sub);
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, variablesScope);  
        List<VariableDeclaration>  bdVars      = new ArrayList<>();
        List<Expression>                bdVarExprs  = new ArrayList<>();
        
        for(Sort sort : sorts)
        {
            String name = TranslatorUtils.getNewName();
            VariableDeclaration bdVar;
            Expression bdVarExpr;
            
            if(sort instanceof IntSort)
            {
                bdVar = new VariableDeclaration(name, getTranslator().uninterpretedInt);
                bdVarExpr = mkTupleSelExpr(mkUnaryIntTupValue(bdVar.getVariable()), 0);
            }
            else
            {
                bdVar = new VariableDeclaration(name, getTranslator().atomSort);
                bdVarExpr = bdVar.getVariable();
            }
            bdVars.add(bdVar);
            bdVarExprs.add(bdVarExpr);
        }
        Expression bdVarTupExpr = mkOneTupleExprOutofAtoms(bdVarExprs);
        Expression bdVarSetExpr = mkSingleton(bdVarTupExpr);
        Expression bodyExpr     = new BinaryExpression(set, BinaryExpression.Op.SUBSET, bdVarSetExpr);
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        
        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return tryAddingExistentialConstraint(exists);
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
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
    }
    
    public UnaryExpression mkSingleton(Expression tuple)
    {
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
    }
    
    public MultiArityExpression mkTupleExpr(List<VariableDeclaration> bdVarDecls)
    {
        List<Expression> constExprs = new ArrayList<>();
        for(VariableDeclaration varDecl : bdVarDecls)
        {
            constExprs.add(varDecl.getVariable());
        }
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExprs);
    }  
    
    public Expression mkTupleSelExpr(Expression expr, int index)
    {
        return new BinaryExpression(IntConstant.getInstance(index), BinaryExpression.Op.TUPSEL, expr);
    }
    
    public Expression mkUnaryIntTupValue(Expression expr)
    {
        return new FunctionCallExpression(getTranslator().getFunction(valueOfUnaryIntTup), expr);
    }

    private Alloy2SmtTranslator getTranslator() 
    {
        return exprTranslator.translator;
    }

}
