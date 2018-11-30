package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.smtAst.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import java.util.Map;

public class ExprBinaryTranslator
{
    final ExprTranslator exprTranslator;

    public ExprBinaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
    }

    Expression translateExprBinary(ExprBinary expr, Map<String, Expression> variablesScope)
    {
        switch (expr.op)
        {
            case ARROW              : return translateArrow(expr, variablesScope);
            case ANY_ARROW_SOME     : throw new UnsupportedOperationException();
            case ANY_ARROW_ONE      : throw new UnsupportedOperationException();
            case ANY_ARROW_LONE     : throw new UnsupportedOperationException();
            case SOME_ARROW_ANY     : throw new UnsupportedOperationException();
            case SOME_ARROW_SOME    : throw new UnsupportedOperationException();
            case SOME_ARROW_ONE     : throw new UnsupportedOperationException();
            case SOME_ARROW_LONE    : throw new UnsupportedOperationException();
            case ONE_ARROW_ANY      : throw new UnsupportedOperationException();
            case ONE_ARROW_SOME     : throw new UnsupportedOperationException();
            case ONE_ARROW_ONE      : throw new UnsupportedOperationException();
            case ONE_ARROW_LONE     : throw new UnsupportedOperationException();
            case LONE_ARROW_ANY     : throw new UnsupportedOperationException();
            case LONE_ARROW_SOME    : throw new UnsupportedOperationException();
            case LONE_ARROW_ONE     : throw new UnsupportedOperationException();
            case LONE_ARROW_LONE    : throw new UnsupportedOperationException();
            case ISSEQ_ARROW_LONE   : throw new UnsupportedOperationException();
            
            // Relational operators
            case JOIN               : return translateJoin(expr, variablesScope);
            case DOMAIN             : return translateDomainRestriction(expr, variablesScope);
            case RANGE              : return translateRangeRestriction(expr, variablesScope);
            case INTERSECT          : return translateSetOperation(expr, BinaryExpression.Op.INTERSECTION, variablesScope);
            case PLUSPLUS           : return translatePlusPlus(expr, variablesScope);
            case EQUALS             : return translateEqComparison(expr, BinaryExpression.Op.EQ, variablesScope);
            case NOT_EQUALS         : return translateEqComparison(expr, BinaryExpression.Op.NEQ, variablesScope);            

            // Set op
            case PLUS               : return translateSetOperation(expr, BinaryExpression.Op.UNION, variablesScope);
            case MINUS              : return translateSetOperation(expr, BinaryExpression.Op.SETMINUS, variablesScope);
            
            // Arithmetic operators            
            case IPLUS              : return translateArithmetic(expr, BinaryExpression.Op.PLUS, variablesScope);
            case IMINUS             : return translateArithmetic(expr, BinaryExpression.Op.MINUS, variablesScope);
            case MUL                : return translateArithmetic(expr, BinaryExpression.Op.MULTIPLY, variablesScope);
            case DIV                : return translateArithmetic(expr, BinaryExpression.Op.DIVIDE, variablesScope);
            case REM                : throw new UnsupportedOperationException();
            
            // Comparison operators
            case LT                 : return translateComparison(expr, BinaryExpression.Op.LT, variablesScope);
            case LTE                : return translateComparison(expr, BinaryExpression.Op.LTE, variablesScope);
            case GT                 : return translateComparison(expr, BinaryExpression.Op.GT, variablesScope);
            case GTE                : return translateComparison(expr, BinaryExpression.Op.GTE, variablesScope);
            case IN                 : return translateSubsetOperation(expr, BinaryExpression.Op.SUBSET, variablesScope);
            case NOT_IN             : return translateSubsetOperation(expr, null, variablesScope);
            case IMPLIES            : return translateImplies(expr, variablesScope);            
            case AND                : return translateAnd(expr, variablesScope);
            case OR                 : return translateOr(expr, variablesScope);
            case IFF                : return translateEqComparison(expr, BinaryExpression.Op.EQ, variablesScope);
            case NOT_LT             : return translateComparison(expr, BinaryExpression.Op.GTE, variablesScope);
            case NOT_LTE            : return translateComparison(expr, BinaryExpression.Op.GT, variablesScope);
            case NOT_GT             : return translateComparison(expr, BinaryExpression.Op.LTE, variablesScope);
            case NOT_GTE            : return translateComparison(expr, BinaryExpression.Op.LT, variablesScope);
            case SHL                : throw new UnsupportedOperationException();
            case SHA                : throw new UnsupportedOperationException();
            case SHR                : throw new UnsupportedOperationException();            
            default                 : throw new UnsupportedOperationException();
        }
    }

    private Expression translateImplies(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
        Expression implExpr  = new BinaryExpression(left, BinaryExpression.Op.IMPLIES, right);

        return implExpr;
    }
    
    private Expression translateAnd(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
        Expression andExpr  = new BinaryExpression(left, BinaryExpression.Op.AND, right);

        return andExpr;
    }

    private Expression translateOr(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
        Expression orExpr  = new BinaryExpression(left, BinaryExpression.Op.OR, right);

        return orExpr;
    }    
    
    private Expression translateArrow(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
        Expression product  = new BinaryExpression(left, BinaryExpression.Op.PRODUCT, right);

        return product;
    }

    private Expression translatePlusPlus(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        int rightExprArity  =  expr.right.type().arity();
        if( rightExprArity == 1)
        {
            // ++ is like a single + with arity 1 (i.e. is like a union)
            return translateSetOperation(expr, BinaryExpression.Op.UNION, variablesScope);
        }
        else 
        {
            Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
            Expression join     = right;            
            
            for(int i = 0; i < rightExprArity-1; ++i)
            {
                join = new BinaryExpression(join, BinaryExpression.Op.JOIN, exprTranslator.translator.atomUniv.getConstantExpr());
            }
            for(int i = 0; i < rightExprArity-1; ++i)
            {
                join = new BinaryExpression(join, BinaryExpression.Op.PRODUCT, exprTranslator.translator.atomUniv.getConstantExpr());
            }            
            
            Expression intersection         = new BinaryExpression(join, BinaryExpression.Op.INTERSECTION, left);
            Expression difference           = new BinaryExpression(left, BinaryExpression.Op.SETMINUS, intersection);
            Expression union                = new BinaryExpression(difference, BinaryExpression.Op.UNION, right);

            return union;

        }
    }

    private Expression translateDomainRestriction(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        int arity = expr.right.type().arity();

        if(arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            Expression left = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression right = exprTranslator.translateExpr(expr.right, variablesScope);

            for(int i = 0; i < arity - 1; ++i)
            {
                left = new BinaryExpression(left, BinaryExpression.Op.PRODUCT, exprTranslator.translator.atomUniv.getConstantExpr());
            }
            BinaryExpression    intersection    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);
            return intersection;
        }
    }

    private Expression translateRangeRestriction(ExprBinary expr, Map<String,Expression> variablesScope)
    {
        int arity = expr.left.type().arity();

        if(arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            Expression          left            = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression          right           = exprTranslator.translateExpr(expr.right, variablesScope);
            
            for(int i = 0; i < arity - 1; ++i)
            {
                right = new BinaryExpression(exprTranslator.translator.atomUniv.getConstantExpr(), BinaryExpression.Op.PRODUCT, right);
            }            

            BinaryExpression    intersection    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);

            return intersection;
        }
    }

    public Expression translateArithmetic(ExprBinary expr, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {
        Expression leftExpr     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression rightExpr    = exprTranslator.translateExpr(expr.right, variablesScope);    
        
        if(!exprTranslator.translator.arithOps.containsKey(op))
        {
            BoundVariableDeclaration  bdIntVar1 = new BoundVariableDeclaration("x", exprTranslator.translator.unaryIntSort);
            BoundVariableDeclaration  bdIntVar2 = new BoundVariableDeclaration("y", exprTranslator.translator.unaryIntSort); 
            BoundVariableDeclaration  bdIntVar3 = new BoundVariableDeclaration("z", exprTranslator.translator.unaryIntSort); 
            Expression memUniv1 = new BinaryExpression(bdIntVar1.getConstantExpr(), BinaryExpression.Op.MEMBER, exprTranslator.translator.intUniv.getConstantExpr());
            Expression memUniv2 = new BinaryExpression(bdIntVar2.getConstantExpr(), BinaryExpression.Op.MEMBER, exprTranslator.translator.intUniv.getConstantExpr());
            Expression memUniv3 = new BinaryExpression(bdIntVar3.getConstantExpr(), BinaryExpression.Op.MEMBER, exprTranslator.translator.intUniv.getConstantExpr());            
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
                    arithVarDecl = new ConstantDeclaration("PLUS", exprTranslator.translator.ternaryIntSort);
                    Expression plusExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.PLUS, bdIntVar2Expr);
                    plusExpr = new BinaryExpression(plusExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, plusExpr); 
                    rhsExpr = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);
                    break;
                case MINUS:
                    arithVarDecl = new ConstantDeclaration("MINUS", exprTranslator.translator.ternaryIntSort);
                    Expression minusExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MINUS, bdIntVar2Expr);
                    minusExpr = new BinaryExpression(minusExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, minusExpr); 
                    rhsExpr = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);             
                    break;
                case MULTIPLY:
                    arithVarDecl = new ConstantDeclaration("MUL", exprTranslator.translator.ternaryIntSort);
                    Expression mulExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MULTIPLY, bdIntVar2Expr);
                    mulExpr = new BinaryExpression(mulExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, mulExpr); 
                    rhsExpr = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);
                  
                    break;
                case DIVIDE:
                    arithVarDecl = new ConstantDeclaration("DIV", exprTranslator.translator.ternaryIntSort);
                    Expression divExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.DIVIDE, bdIntVar2Expr);                    
                    divExpr = new BinaryExpression(divExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, divExpr); 
                    lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(bdIntVar2Expr, BinaryExpression.Op.EQ, new IntConstant(0))));
                    rhsExpr = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(bdIntVar1, bdIntVar2, bdIntVar3), BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                    finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, rhsExpr), bdIntVar1, bdIntVar2, bdIntVar3);                 
                    break;
                default:
                    break;                   
            }
            exprTranslator.translator.smtProgram.addConstantDeclaration(arithVarDecl);
            exprTranslator.translator.smtProgram.addAssertion(new Assertion(finalExpr));     
            exprTranslator.translator.arithOps.put(op, arithVarDecl.getConstantExpr());
        }
        return new BinaryExpression(leftExpr, BinaryExpression.Op.JOIN, new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, exprTranslator.translator.arithOps.get(op)));
    }
    
    private Expression translateComparison(ExprBinary expr, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {
        Expression comparisonExpr = null;   
        
        // Right hand side is a expression and right hand side is a constant
        if(((expr.left instanceof ExprUnary) && ((ExprUnary)expr.left).op == ExprUnary.Op.CARDINALITY && 
                (expr.right instanceof ExprConstant)))
        {            
            int n               = ((ExprConstant)expr.right).num;  
            int arity           = ((ExprUnary)expr.left).sub.type().arity();                                    
            Expression leftExpr = exprTranslator.translateExpr(((ExprUnary)expr.left).sub, variablesScope);    
            
            List<Expression>                existentialBdVarExprs   = new ArrayList<>();               
            List<BoundVariableDeclaration>  existentialBdVars       = new ArrayList<>();     
            List<Sort> leftExprSorts = exprTranslator.getExprSorts(((ExprUnary)expr.left).sub);
            
            switch(op)
            {
                case GT:{  
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n+1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n+1);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        

                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  rightExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.getEmptyRelationOfSort(leftExprSorts);
                    }
                    
                    // rightExpr + 1 <= leftExpr
                    comparisonExpr = new BinaryExpression(rightExpr, BinaryExpression.Op.SUBSET, leftExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }                    
                    break;
                }
                case LT:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n-1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n-1);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  rightExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.getEmptyRelationOfSort(leftExprSorts);
                    }
                    
                    // leftExpr <= rightExpr-1
                    comparisonExpr = new BinaryExpression(leftExpr, BinaryExpression.Op.SUBSET, rightExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    } 
                    break;
                }
                case GTE:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  rightExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.getEmptyRelationOfSort(leftExprSorts);
                    }
                    
                    // rightExpr <= leftExpr
                    comparisonExpr = new BinaryExpression(rightExpr, BinaryExpression.Op.SUBSET, leftExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }
                    break;
                }
                case LTE:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  rightExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.getEmptyRelationOfSort(leftExprSorts);
                    }
                    
                    // rightExpr <= leftExpr
                    comparisonExpr = new BinaryExpression(leftExpr, BinaryExpression.Op.SUBSET, rightExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }
                    break;                    
                }                
                default:break;
            }  
        }
        else if((expr.right instanceof ExprUnary) && ((ExprUnary)expr.right).op == ExprUnary.Op.CARDINALITY && 
                (expr.left instanceof ExprConstant)) 
        {
            int n               = ((ExprConstant)expr.left).num;  
            int arity           = ((ExprUnary)expr.right).sub.type().arity();                                    
            Expression rightExpr = exprTranslator.translateExpr(((ExprUnary)expr.right).sub, variablesScope);    
            
            List<Expression>                existentialBdVarExprs   = new ArrayList<>();               
            List<BoundVariableDeclaration>  existentialBdVars       = new ArrayList<>();     
            List<Sort> rightExprSorts = exprTranslator.getExprSorts(((ExprUnary)expr.right).sub);
            
            switch(op)
            {
                case GT:{  
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n+1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n+1);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        

                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  leftExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.getEmptyRelationOfSort(rightExprSorts);
                    }
                    
                    // rightExpr + 1 <= leftExpr
                    comparisonExpr = new BinaryExpression(rightExpr, BinaryExpression.Op.SUBSET, leftExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }                    
                    break;
                }
                case LT:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n-1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n-1);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  leftExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.getEmptyRelationOfSort(rightExprSorts);
                    }
                    
                    // leftExpr <= rightExpr-1
                    comparisonExpr = new BinaryExpression(rightExpr, BinaryExpression.Op.SUBSET, leftExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    } 
                    break;
                }
                case GTE:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  leftExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.getEmptyRelationOfSort(rightExprSorts);
                    }
                    
                    // rightExpr <= leftExpr
                    comparisonExpr = new BinaryExpression(rightExpr, BinaryExpression.Op.SUBSET, leftExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }
                    break;
                }
                case LTE:{
                    if(arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n);
                    }

                    for(BoundVariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getConstantExpr());
                    }        
                    
                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.mkDistinctExpr(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
                    if(exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }
     
                    Expression  leftExpr;

                    if(existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.getEmptyRelationOfSort(rightExprSorts);
                    }
                    
                    // leftExpr <= rightExpr 
                    comparisonExpr = new BinaryExpression(leftExpr, BinaryExpression.Op.SUBSET, rightExpr);
                    comparisonExpr = new BinaryExpression(comparisonExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    
                    if(!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
                    }
                    break;                    
                }                
                default:break;
            }  
        }
        else 
        {
            Expression leftExpr     = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression rightExpr    = exprTranslator.translateExpr(expr.right, variablesScope);

            if(!exprTranslator.translator.comparisonOps.containsKey(op))
            {
                BoundVariableDeclaration    bdIntRelVar1        = new BoundVariableDeclaration("_rel1", exprTranslator.translator.setOfUnaryIntSort);                
                BoundVariableDeclaration    bdIntRelVar2        = new BoundVariableDeclaration("_rel2", exprTranslator.translator.setOfUnaryIntSort);
                BoundVariableDeclaration    bdIntVar1           = new BoundVariableDeclaration("_x_int", exprTranslator.translator.intSort);
                BoundVariableDeclaration    bdIntVar2           = new BoundVariableDeclaration("_y_int", exprTranslator.translator.intSort);     
                ConstantExpression          bdIntVar1Expr       = new ConstantExpression(bdIntVar1);
                ConstantExpression          bdIntVar2Expr       = new ConstantExpression(bdIntVar2);
                ConstantExpression          bdIntRelVar1Expr    = new ConstantExpression(bdIntRelVar1);
                ConstantExpression          bdIntRelVar2Expr    = new ConstantExpression(bdIntRelVar2);     
                FunctionDefinition          compFunc            = null;

                Expression funcExpr = new BinaryExpression(exprTranslator.getSingleton(bdIntVar1Expr), BinaryExpression.Op.EQ, bdIntRelVar1Expr);
                funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(exprTranslator.getSingleton(bdIntVar2Expr), BinaryExpression.Op.EQ, bdIntRelVar2Expr));

                switch(op)
                {
                    case GT:
                        funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.GT, bdIntVar2Expr));
                        compFunc = new FunctionDefinition("GT", new BoolSort(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntVar1, bdIntVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);                
                        break;
                    case LT:
                        funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.LT, bdIntVar2Expr));
                        compFunc = new FunctionDefinition("LT", new BoolSort(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntVar1, bdIntVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);                
                        break;
                    case GTE:
                        funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.GTE, bdIntVar2Expr));
                        compFunc = new FunctionDefinition("GTE", new BoolSort(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntVar1, bdIntVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);                
                        break;
                    case LTE:
                        funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.LTE, bdIntVar2Expr));
                        compFunc = new FunctionDefinition("LTE", new BoolSort(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntVar1, bdIntVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);                                        
                        break;
                    default:break;
                } 
                exprTranslator.translator.smtProgram.addFcnDef(compFunc);
                exprTranslator.translator.comparisonOps.put(op, compFunc);
            }
            comparisonExpr = new FunctionCallExpression(exprTranslator.translator.comparisonOps.get(op).getFuncName(), leftExpr, rightExpr);             
            if(!exprTranslator.translator.existentialBdVars.isEmpty())
            {
                if(exprTranslator.translator.auxExpr != null)
                {
                    comparisonExpr = new BinaryExpression(comparisonExpr, op, exprTranslator.translator.auxExpr);
                }
                comparisonExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, comparisonExpr);
            }
            exprTranslator.translator.auxExpr = null;
            exprTranslator.translator.existentialBdVars.clear();
        }    

        return comparisonExpr;     
    }
    
    private Expression translateEqComparison(ExprBinary expr, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {

        if(   (expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY) ||
                (expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
            )
        {
            return translateCardinality(expr, op, variablesScope);
        }


        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }

        Expression finalExpr;
        
        if(op == BinaryExpression.Op.NEQ)
        {
            finalExpr = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(left, BinaryExpression.Op.EQ, right));
        }
        else
        { 
            finalExpr = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
        }        

        if(!exprTranslator.translator.existentialBdVars.isEmpty())
        {
            if(exprTranslator.translator.auxExpr != null)
            {
                finalExpr = new BinaryExpression(finalExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                exprTranslator.translator.auxExpr = null;
            }
            finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, finalExpr);
        }                
        return finalExpr;        
    }

    private Expression translateCardinality(ExprBinary expr, BinaryExpression.Op op , Map<String, Expression> variablesScope)
    {
        // CVC4 doesn't support comparison  between 2 cardinality expressions
        if
            (   expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY
            )
        {
            throw new UnsupportedOperationException("CVC4 doesn't support comparision between 2 cardinality expressions.");
        }

        if
            (
                (expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                (!(expr.right instanceof ExprConstant &&
                        ((ExprConstant) expr.right).op == ExprConstant.Op.NUMBER))) ||
                (expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY &&
                (!(expr.left instanceof ExprConstant &&
                        ((ExprConstant) expr.left).op == ExprConstant.Op.NUMBER)))
            )
        {
            throw new UnsupportedOperationException("CVC4 only supports cardinality with numbers");
        }


        // translate cardinality differently
        if
            (   (expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY)
            )
        {
            int         n           = ((ExprConstant)expr.right).num;
            Expression  equality = translateEqCardComparison((ExprUnary) expr.left, n, op, variablesScope);
            return equality;
        }

        if
            (   (expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
            )
        {
            int         n           = ((ExprConstant)expr.left).num;
            Expression  equality = translateEqCardComparison((ExprUnary) expr.right, n, op, variablesScope);
            return equality;
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateEqCardComparison(ExprUnary expr, int n, BinaryExpression.Op op ,Map<String, Expression> variablesScope)
    {
        int arity = expr.type().arity();        
        List<Expression> existentialBdVarExprs = new ArrayList<>();
        List<BoundVariableDeclaration> existentialBdVars = new ArrayList<>(); 
        List<Sort> exprSorts = exprTranslator.getExprSorts(expr);
        
        if(arity == 1)
        {
            existentialBdVars = exprTranslator.getBdVars(exprSorts.get(0), n);
        }
        else
        {
            existentialBdVars = exprTranslator.getBdTupleVars(exprSorts, arity, n);
        }
        
        for(BoundVariableDeclaration bdVar : existentialBdVars)
        {
            existentialBdVarExprs.add(bdVar.getConstantExpr());
        }        
        
        Expression distElementsExpr = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, existentialBdVarExprs);
        
        exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
        if(exprTranslator.translator.auxExpr != null)
        {
            exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
        }
        else
        {
            exprTranslator.translator.auxExpr = distElementsExpr;
        }
        
        Expression  distElementSetExpr = exprTranslator.getUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);        
        Expression  left    = exprTranslator.translateExpr(expr.sub, variablesScope);
        Expression  right   = distElementSetExpr;
        
        switch (op)
        {
            case NEQ:
            case EQ : {
                Expression eqExpr = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
                
                if(exprTranslator.translator.auxExpr != null)
                {
                    eqExpr = new BinaryExpression(eqExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                    exprTranslator.translator.auxExpr = null;
                }
                if(!exprTranslator.translator.existentialBdVars.isEmpty())
                {
                    eqExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, existentialBdVars, eqExpr);
                    exprTranslator.translator.existentialBdVars.clear();
                }
                if(op == BinaryExpression.Op.NEQ)
                {
                    eqExpr = new UnaryExpression(UnaryExpression.Op.NOT, eqExpr);
                }
                return eqExpr;
            }
            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expression translateSetOperation(ExprBinary expr, BinaryExpression.Op op, Map<String, Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }

        BinaryExpression operation = new BinaryExpression(left, op, right);
        return operation;
    }
    
    private Expression translateSubsetOperation(ExprBinary expr, BinaryExpression.Op op, Map<String, Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }
                
        Expression finalExpr = new BinaryExpression(left, BinaryExpression.Op.SUBSET, right);
        
        if(op == null)
        {
            finalExpr = new UnaryExpression(UnaryExpression.Op.NOT, finalExpr);
        }
        if(!exprTranslator.translator.existentialBdVars.isEmpty())
        {
            if(exprTranslator.translator.auxExpr != null)
            {
                finalExpr = new BinaryExpression(finalExpr, BinaryExpression.Op.AND, exprTranslator.translator.auxExpr);
                exprTranslator.translator.auxExpr = null;
            }
            finalExpr = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, exprTranslator.translator.existentialBdVars, finalExpr);
            exprTranslator.translator.existentialBdVars.clear();
        }                
        return finalExpr;                 
    }

    private Expression translateJoin(ExprBinary expr, Map<String, Expression> variablesScope)
    {
        Expression          left    = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression          right   = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration &&
                (!(((ConstantExpression)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration  &&
                (!(((ConstantExpression)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }
        BinaryExpression    join    = new BinaryExpression(left, BinaryExpression.Op.JOIN, right);
        return join;
    }
}
