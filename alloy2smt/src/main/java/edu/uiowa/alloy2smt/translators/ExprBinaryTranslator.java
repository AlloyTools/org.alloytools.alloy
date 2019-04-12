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
            case NOT_EQUALS         : return new UnaryExpression(UnaryExpression.Op.NOT, translateEqComparison(expr, BinaryExpression.Op.EQ, variablesScope));

            // Set op
            case PLUS               : return translateSetOperation(expr, BinaryExpression.Op.UNION, variablesScope);
            case MINUS              : return translateSetOperation(expr, BinaryExpression.Op.SETMINUS, variablesScope);
            
            // Arithmetic operators            
            case IPLUS              : return translateArithmetic(expr, BinaryExpression.Op.PLUS, variablesScope);
            case IMINUS             : return translateArithmetic(expr, BinaryExpression.Op.MINUS, variablesScope);
            case MUL                : return translateArithmetic(expr, BinaryExpression.Op.MULTIPLY, variablesScope);
            case DIV                : return translateArithmetic(expr, BinaryExpression.Op.DIVIDE, variablesScope);
            case REM                : return translateArithmetic(expr, BinaryExpression.Op.MOD, variablesScope);
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
                join = new BinaryExpression(join, BinaryExpression.Op.JOIN, exprTranslator.translator.atomUniv.getVariable());
            }
            for(int i = 0; i < rightExprArity-1; ++i)
            {
                join = new BinaryExpression(join, BinaryExpression.Op.PRODUCT, exprTranslator.translator.atomUniv.getVariable());
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
                left = new BinaryExpression(left, BinaryExpression.Op.PRODUCT, exprTranslator.translator.atomUniv.getVariable());
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
            Expression left  = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression right = exprTranslator.translateExpr(expr.right, variablesScope);
            
            for(int i = 0; i < arity - 1; ++i)
            {
                right = new BinaryExpression(exprTranslator.translator.atomUniv.getVariable(), BinaryExpression.Op.PRODUCT, right);
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
            exprTranslator.declArithmeticOp(op);
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
            List<VariableDeclaration>  existentialBdVars       = new ArrayList<>();
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
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
            List<VariableDeclaration>  existentialBdVars       = new ArrayList<>();
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
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

                    for(VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
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
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
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
                declComparisonOps(op);
            }
            comparisonExpr = new FunctionCallExpression(exprTranslator.translator.comparisonOps.get(op), leftExpr, rightExpr);
            
            // Add auxiliary quantifiers and expressions
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
    
    private void declComparisonOps(BinaryExpression.Op op)
    {
        VariableDeclaration bdIntRelVar1        = new VariableDeclaration("_rel1", exprTranslator.translator.setOfUninterpretedIntTuple);
        VariableDeclaration bdIntRelVar2        = new VariableDeclaration("_rel2", exprTranslator.translator.setOfUninterpretedIntTuple);
        VariableDeclaration bdIntAtomVar1       = exprTranslator.createVariable(exprTranslator.translator.intSort, "_x_int");
        VariableDeclaration bdIntAtomVar2       = exprTranslator.createVariable(exprTranslator.translator.intSort, "_y_int");
        Expression                  unaryIntTup1        = exprTranslator.exprUnaryTranslator.mkUnaryIntTupValue(bdIntAtomVar1.getVariable());
        Expression                  unaryIntTup2        = exprTranslator.exprUnaryTranslator.mkUnaryIntTupValue(bdIntAtomVar2.getVariable());
        
        Expression          bdIntVar1Expr       = mkTupleSelectExpr(unaryIntTup1, 0);
        Expression          bdIntVar2Expr       = mkTupleSelectExpr(unaryIntTup2, 0);
        Expression          bdIntRelVar1Expr    = new Variable(bdIntRelVar1);
        Expression          bdIntRelVar2Expr    = new Variable(bdIntRelVar2);
        FunctionDefinition  compFunc            = null;

        Expression funcExpr = new BinaryExpression(exprTranslator.mkSingletonOutOfTuple(unaryIntTup1), BinaryExpression.Op.EQ, bdIntRelVar1Expr);
        funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(exprTranslator.mkSingletonOutOfTuple(unaryIntTup2), BinaryExpression.Op.EQ, bdIntRelVar2Expr));

        switch(op)
        {
            case GT:
                funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.GT, bdIntVar2Expr));
                compFunc = new FunctionDefinition("_GT", BoolSort.getInstance(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntAtomVar1, bdIntAtomVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);
                break;
            case LT:
                funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.LT, bdIntVar2Expr));
                compFunc = new FunctionDefinition("_LT", BoolSort.getInstance(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntAtomVar1, bdIntAtomVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);
                break;
            case GTE:
                funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.GTE, bdIntVar2Expr));
                compFunc = new FunctionDefinition("_GTE", BoolSort.getInstance(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntAtomVar1, bdIntAtomVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);
                break;
            case LTE:
                funcExpr = new BinaryExpression(funcExpr, BinaryExpression.Op.AND, new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.LTE, bdIntVar2Expr));
                compFunc = new FunctionDefinition("_LTE", BoolSort.getInstance(), new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, Arrays.asList(bdIntAtomVar1, bdIntAtomVar2), funcExpr), bdIntRelVar1, bdIntRelVar2);
                break;
            default:break;
        } 
        exprTranslator.translator.smtProgram.addFunction(compFunc);
        exprTranslator.translator.comparisonOps.put(op, compFunc);                
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

        if(left instanceof Variable &&
                (!(((Variable)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) left);
        }
        else if(left instanceof MultiArityExpression &&
                ((MultiArityExpression)left).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            left = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)left);
        }
        if(right instanceof Variable &&
                (!(((Variable)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) right);
        }
        else if(right instanceof MultiArityExpression &&
                ((MultiArityExpression)right).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            right = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)right);
        }

        if(right.getSort().equals(Alloy2SmtTranslator.setOfUninterpretedIntTuple) &&
                left.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            left = exprTranslator.translator.handleIntConstant(left);
        }

        if(left.getSort().equals(Alloy2SmtTranslator.setOfUninterpretedIntTuple) &&
                right.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            right = exprTranslator.translator.handleIntConstant(right);
        }



        Expression finalExpr = new BinaryExpression(left, BinaryExpression.Op.EQ, right);


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
        List<VariableDeclaration> existentialBdVars = new ArrayList<>();
        List<Sort> exprSorts = exprTranslator.getExprSorts(expr.sub);
        
        if(arity == 1)
        {
            existentialBdVars = exprTranslator.getBdVars(exprSorts.get(0), n);
        }
        else
        {
            existentialBdVars = exprTranslator.getBdTupleVars(exprSorts, arity, n);
        }
        
        for(VariableDeclaration bdVar : existentialBdVars)
        {
            existentialBdVarExprs.add(bdVar.getVariable());
        }

        Expression distElementsExpr;

        if(existentialBdVarExprs.size() == 1)
        {
            // distinct operator needs at least 2 arguments
            distElementsExpr = new BoolConstant(true);
        }
        else
        {
            distElementsExpr = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, existentialBdVarExprs);
        }
        
        exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);        
        if(exprTranslator.translator.auxExpr != null)
        {
            exprTranslator.translator.auxExpr = new BinaryExpression(exprTranslator.translator.auxExpr, BinaryExpression.Op.AND, distElementsExpr);
        }
        else
        {
            exprTranslator.translator.auxExpr = distElementsExpr;
        }
        
        Expression  distElementSetExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);        
        Expression  left    = exprTranslator.translateExpr(expr.sub, variablesScope);
        Expression  right   = distElementSetExpr;
        
        switch (op)
        {
            case EQ :
            {
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

        if(left instanceof Variable &&
                (!(((Variable)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) left);
        }
        else if(left instanceof MultiArityExpression &&
                ((MultiArityExpression)left).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            left = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)left);
        }
        if(right instanceof Variable &&
                (!(((Variable)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) right);
        }
        else if(right instanceof MultiArityExpression &&
                ((MultiArityExpression)right).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            right = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)right);
        } 

        BinaryExpression operation = new BinaryExpression(left, op, right);
        return operation;
    }
    
    private Expression translateSubsetOperation(ExprBinary expr, BinaryExpression.Op op, Map<String, Expression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof Variable &&
                (!(((Variable)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) left);
        }
        else if(left instanceof MultiArityExpression &&
                ((MultiArityExpression)left).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            left = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)left);
        }
        if(right instanceof Variable &&
                (!(((Variable)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) right);
        }
        else if(right instanceof MultiArityExpression &&
                ((MultiArityExpression)right).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            right = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)right);
        }

        if(right.getSort().equals(Alloy2SmtTranslator.setOfUninterpretedIntTuple) &&
                left.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            left = exprTranslator.translator.handleIntConstant(left);
        }

        if(left.getSort().equals(Alloy2SmtTranslator.setOfUninterpretedIntTuple) &&
                right.getSort().equals(Alloy2SmtTranslator.setOfIntSortTuple))
        {
            right = exprTranslator.translator.handleIntConstant(right);
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

        if(left instanceof Variable &&
                (!(((Variable)left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) left);
        }
        else if(left instanceof MultiArityExpression &&
                ((MultiArityExpression)left).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            left = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)left);
        }
        if(right instanceof Variable &&
                (!(((Variable)right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = exprTranslator.mkSingletonOutOfTupleOrAtom((Variable) right);
        }
        else if(right instanceof MultiArityExpression &&
                ((MultiArityExpression)right).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            right = exprTranslator.mkSingletonOutOfTuple((MultiArityExpression)right);
        }        
        BinaryExpression    join    = new BinaryExpression(left, BinaryExpression.Op.JOIN, right);
        return join;
    }
    
    public Expression mkTupleSelectExpr(Expression tupleExpr, int index)
    {
        return new BinaryExpression(IntConstant.getInstance(index), BinaryExpression.Op.TUPSEL, tupleExpr);
    }    
}
