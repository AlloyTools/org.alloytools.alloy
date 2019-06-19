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
import java.util.List;
import java.util.Map;

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
            case LONEOF     : return exprTranslator.translateExpr(exprUnary.sub, environment);
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
        Expression not          = new UnaryExpression(UnaryExpression.Op.NOT, expression);
        return not;
    }

    private Expression translateClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression closure     = new UnaryExpression(UnaryExpression.Op.TCLOSURE, expression);
        return closure;
    }

    private Expression translateReflexiveClosure(ExprUnary exprUnary, Environment environment)
    {
        Expression          closure             = translateClosure(exprUnary, environment);
        BinaryExpression    reflexiveClosure    = new BinaryExpression(closure, BinaryExpression.Op.UNION, AbstractTranslator.atomIdentity.getVariable());
        return reflexiveClosure;
    }

    private Expression translateTranspose(ExprUnary exprUnary, Environment environment)
    {
        Expression      expression  = exprTranslator.translateExpr(exprUnary.sub, environment);
        UnaryExpression transpose   = new UnaryExpression(UnaryExpression.Op.TRANSPOSE, expression);
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
                        return new UnaryExpression(UnaryExpression.Op.SINGLETON, new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    }                    
                    else if(((Variable)constExpr).getDeclaration().getSort() == AbstractTranslator.intSort)
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
            finalExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, finalExpr);
            finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, translator.existentialBdVars, finalExpr);
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
        Expression eqExpr = new BinaryExpression(set, BinaryExpression.Op.EQ, 
                                    new UnaryExpression(UnaryExpression.Op.EMPTYSET, new SetSort(new TupleSort(elementSorts))));         
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
        Expression bodyExpr         = new BinaryExpression(bdVarTupExpr, BinaryExpression.Op.MEMBER, someRel);
        
        // If the expression is a binary or ternary field, we need to make sure 
        // there exists a var of type binaryIntTup such that the integer tuple equals to the bdVarTupExpr.
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        

        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
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
        Expression bodyExpr     = new BinaryExpression(bdVarSetExpr, BinaryExpression.Op.EQ, set);
//        bodyExpr = addConstraintForBinAndTerIntRel(bdVarTupExpr, exprUnary.sub, bodyExpr);
        
        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return tryAddingExistentialConstraint(exists);
    }
    
    private Expression translateOneOf(ExprUnary exprUnary, Environment environment)
    {
        Expression set = exprTranslator.translateExpr(exprUnary.sub, environment);

        return set;
    }    

    private Expression translateLone(ExprUnary exprUnary, Environment environment)
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
        return new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, expr);
    }
}
