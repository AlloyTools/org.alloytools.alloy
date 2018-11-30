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
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ExprUnaryTranslator
{
    final ExprTranslator exprTranslator;

    public ExprUnaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
    }

    Expression translateExprUnary(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        switch (exprUnary.op)
        {
            case NOOP       : return translateNoop(exprUnary, variablesScope);
            case NO         : return translateNo(exprUnary, variablesScope);
            case SOME       : return translateSome(exprUnary, variablesScope);
            case ONE        : return translateOne(exprUnary, variablesScope);
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
        BinaryExpression    reflexiveClosure    = new BinaryExpression(closure, BinaryExpression.Op.UNION, exprTranslator.translator.atomIden.getConstantExpr());
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
                    case "univ": return exprTranslator.translator.atomUniv.getConstantExpr();
                    case "iden": return exprTranslator.translator.atomIden.getConstantExpr();
                    case "none": return exprTranslator.translator.atomNone.getConstantExpr();
                    case "Int": throw new UnsupportedOperationException("We do not support signature Int used in facts!");
                    default:
                        throw new UnsupportedOperationException();
                }
            }
            else
            {
                return exprTranslator.translator.signaturesMap.get(((Sig) exprUnary.sub)).getConstantExpr();
            }
        }

        if(exprUnary.sub instanceof Sig.Field)
        {
            return exprTranslator.translator.fieldsMap.get(((Sig.Field) exprUnary.sub)).getConstantExpr();
        }

        if(exprUnary.sub instanceof ExprVar)
        {
            if(variablesScope.containsKey(((ExprVar)exprUnary.sub).label))
            {
                Expression constExpr = variablesScope.get(((ExprVar)exprUnary.sub).label);
                
                if(constExpr instanceof ConstantExpression)
                {
                    if(((ConstantExpression)constExpr).getDeclaration().getSort() == exprTranslator.translator.atomSort)
                    {
                        return new UnaryExpression(UnaryExpression.Op.SINGLETON, new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExpr));
                    }                    
                }                
                return constExpr;
            }
            else
            {
                System.out.println("Something is wrong here, we do not have variable declarations in scope: " + ((ExprVar)exprUnary.sub).label);
                throw new RuntimeException();
            }            
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
            return exprTranslator.exprBinaryTranslator.translateExprBinary((ExprBinary) exprUnary.sub, variablesScope);
        }
        
        if(exprUnary.sub instanceof ExprLet)
        {
            return exprTranslator.translateExprLet((ExprLet) exprUnary.sub, variablesScope);
        }  
        
        if(exprUnary.sub instanceof ExprConstant)
        {
            return exprTranslator.translateExprConstant((ExprConstant) exprUnary.sub, variablesScope);
        } 
        
        if(exprUnary.sub instanceof ExprCall)
        {
            return exprTranslator.translateExprCall((ExprCall) exprUnary.sub, variablesScope);
        }         

        throw new UnsupportedOperationException(((ExprLet) exprUnary.sub).toString());
    }

    private Expression translateNo(ExprUnary exprUnary, Map<String, Expression> variablesScope)
    {
        int arity           = exprUnary.sub.type().arity();
        Expression set      = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        Expression eqExpr   = new BinaryExpression(set, BinaryExpression.Op.EQ, exprTranslator.translator.atomNone.getConstantExpr());        
        
        if(arity > 1)
        {
            List<Sort> elementSorts = new ArrayList<>();
            
            for(int i = 0; i < arity; i++)
            {
                elementSorts.add(exprTranslator.translator.atomSort);
            }
            eqExpr = new BinaryExpression(set, BinaryExpression.Op.EQ, 
                                        new UnaryExpression(UnaryExpression.Op.EMPTYSET, new SetSort(new TupleSort(elementSorts))));        
        }        
        return eqExpr;
    }

    private Expression translateSome(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        List<BoundVariableDeclaration>  variables   = getQuantifiedVariables(exprUnary.sub);
        List<Expression>                expressions = variables.stream().map(v -> v.getConstantExpr()).collect(Collectors.toList());
        MultiArityExpression            tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
        Expression                      set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression                member      = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
        QuantifiedExpression            exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, variables, member);
        return exists;
    }

    private List<BoundVariableDeclaration> getQuantifiedVariables(Expr expr)
    {
        List<BoundVariableDeclaration> variables = new ArrayList<>(expr.type().arity());

        for (int i = 0; i < expr.type().arity() ; i++)
        {
               BoundVariableDeclaration variable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), exprTranslator.translator.atomSort);
               variables.add(variable);
        }
        return variables;
    }

    private Expression translateOne(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        List<BoundVariableDeclaration>  variables   = getQuantifiedVariables(exprUnary.sub);
        List<Expression>                expressions = variables.stream().map(v -> v.getConstantExpr()).collect(Collectors.toList());
        Expression                      singleton   = exprTranslator.getSingletonOutOfAtoms(expressions);
        Expression                      set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression                eq          = new BinaryExpression(singleton, BinaryExpression.Op.EQ, set);
        QuantifiedExpression            exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, variables, eq);
        return exists;
    }

    private Expression translateLone(ExprUnary exprUnary, Map<String,Expression> variablesScope)
    {
        List<BoundVariableDeclaration>  variables   = getQuantifiedVariables(exprUnary.sub);
        List<Expression>                expressions = variables.stream().map(v -> v.getConstantExpr()).collect(Collectors.toList());
        Expression                      singleton   = exprTranslator.getSingletonOutOfAtoms(expressions);
        Expression                      set         = exprTranslator.translateExpr(exprUnary.sub, variablesScope);
        BinaryExpression                subset      = new BinaryExpression(set, BinaryExpression.Op.SUBSET, singleton);
        QuantifiedExpression            exists      = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, variables, subset);
        return exists;
    }
    
    public MultiArityExpression mkTupleExpr(BoundVariableDeclaration bdVarDecl)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVarDecl.getConstantExpr());
    }
    
    public MultiArityExpression mkTupleExprOutofAtoms(Expression ... exprs)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
    } 
    
    public MultiArityExpression mkTupleExprOutofUnaryTuples(Expression ... exprs)
    {
        List<Expression> atomExprs = new ArrayList<>();
        
        for(Expression e : exprs)
        {
            atomExprs.add(new BinaryExpression(new IntConstant(0), BinaryExpression.Op.TUPSEL, e));
        }
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
    }     
    
    public UnaryExpression mkSingleton(BoundVariableDeclaration bdVarDecl)
    {
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, mkTupleExpr(bdVarDecl));
    }    
    
    public UnaryExpression mkSingleton(BoundVariableDeclaration ... bdVarDecls)
    {
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, mkTupleExpr(bdVarDecls));
    } 
    
    public UnaryExpression mkSingleton(MultiArityExpression tuple)
    {
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
    }     
    
    public MultiArityExpression mkTupleExpr(BoundVariableDeclaration ... bdVarDecls)
    {
        List<Expression> constExprs = new ArrayList<>();
        for(BoundVariableDeclaration varDecl : bdVarDecls)
        {
            constExprs.add(varDecl.getConstantExpr());
        }
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExprs);
    } 
    
    public MultiArityExpression mkTupleExpr(List<BoundVariableDeclaration> bdVarDecls)
    {
        List<Expression> constExprs = new ArrayList<>();
        for(BoundVariableDeclaration varDecl : bdVarDecls)
        {
            constExprs.add(varDecl.getConstantExpr());
        }
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constExprs);
    }     
}
