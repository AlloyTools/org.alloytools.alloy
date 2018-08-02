package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.Map;

public class ExprBinaryTranslator
{
    final ExprTranslator exprTranslator;

    public ExprBinaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
    }

    Expression translateExprBinary(ExprBinary expr, Map<String, ConstantExpression> variablesScope)
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
            case JOIN               : return translateJoin(expr, variablesScope);
            case DOMAIN             : return translateDomainRestriction(expr, variablesScope);
            case RANGE              : return translateRangeRestriction(expr, variablesScope);
            case INTERSECT          : return translateSetOperation(expr, BinaryExpression.Op.INTERSECTION, variablesScope);
            case PLUSPLUS           : return translatePlusPlus(expr, variablesScope);
            case PLUS               : return translateSetOperation(expr, BinaryExpression.Op.UNION, variablesScope);
            case IPLUS              : throw new UnsupportedOperationException();
            case MINUS              : return translateSetOperation(expr, BinaryExpression.Op.SETMINUS, variablesScope);
            case IMINUS             : throw new UnsupportedOperationException();
            case MUL                : throw new UnsupportedOperationException();
            case DIV                : throw new UnsupportedOperationException();
            case REM                : throw new UnsupportedOperationException();
            case EQUALS             : return translateComparison(expr, BinaryExpression.Op.EQ, variablesScope);
            case NOT_EQUALS         : return translateComparison(expr, BinaryExpression.Op.NEQ, variablesScope);
            case IMPLIES            : throw new UnsupportedOperationException();
            case LT                 : return translateComparison(expr, BinaryExpression.Op.LT, variablesScope);
            case LTE                : return translateComparison(expr, BinaryExpression.Op.LTE, variablesScope);
            case GT                 : return translateComparison(expr, BinaryExpression.Op.GT, variablesScope);
            case GTE                : return translateComparison(expr, BinaryExpression.Op.GTE, variablesScope);
            case NOT_LT             : throw new UnsupportedOperationException();
            case NOT_LTE            : throw new UnsupportedOperationException();
            case NOT_GT             : throw new UnsupportedOperationException();
            case NOT_GTE            : throw new UnsupportedOperationException();
            case SHL                : throw new UnsupportedOperationException();
            case SHA                : throw new UnsupportedOperationException();
            case SHR                : throw new UnsupportedOperationException();
            case IN                 : return translateSetOperation(expr, BinaryExpression.Op.SUBSET, variablesScope);
            case NOT_IN             : return new UnaryExpression(UnaryExpression.Op.NOT, translateSetOperation(expr, BinaryExpression.Op.SUBSET, variablesScope));
            case AND                : throw new UnsupportedOperationException();
            case OR                 : throw new UnsupportedOperationException();
            case IFF                : throw new UnsupportedOperationException();
            default                 : throw new UnsupportedOperationException();
        }
    }

    private Expression translateArrow(ExprBinary expr, Map<String,ConstantExpression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);
        Expression product  = new BinaryExpression(left, BinaryExpression.Op.PRODUCT, right);

        return product;
    }

    private Expression translatePlusPlus(ExprBinary expr, Map<String,ConstantExpression> variablesScope)
    {
        int arity  =  expr.right.type().arity();
        if( arity == 1)
        {
            // ++ is like a single + with arity 1 (i.e. is like a union)
            return translateSetOperation(expr, BinaryExpression.Op.UNION, variablesScope);
        }

        if(arity == 2)
        {
            Expression left                 = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression right                = exprTranslator.translateExpr(expr.right, variablesScope);
            Expression join               = new BinaryExpression(right, BinaryExpression.Op.JOIN, exprTranslator.translator.universe);
            Expression product              = new BinaryExpression(join, BinaryExpression.Op.PRODUCT, exprTranslator.translator.universe);
            Expression intersection         = new BinaryExpression(product, BinaryExpression.Op.INTERSECTION, left);
            Expression difference           = new BinaryExpression(left, BinaryExpression.Op.SETMINUS, intersection);
            Expression union                = new BinaryExpression(difference, BinaryExpression.Op.UNION, right);

            return union;

        }

        throw new UnsupportedOperationException();
    }

    private Expression translateDomainRestriction(ExprBinary expr, Map<String,ConstantExpression> variablesScope)
    {
        int arity = expr.right.type().arity();

        if(arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else if(arity == 2)
        {
            Expression          left            = exprTranslator.translateExpr(expr.left, variablesScope);
            BinaryExpression    product         = new BinaryExpression(left, BinaryExpression.Op.PRODUCT, exprTranslator.translator.universe);
            Expression          right           = exprTranslator.translateExpr(expr.right, variablesScope);
            BinaryExpression    intersection    = new BinaryExpression(product, BinaryExpression.Op.INTERSECTION, right);
            return intersection;
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateRangeRestriction(ExprBinary expr, Map<String,ConstantExpression> variablesScope)
    {
        int arity = expr.left.type().arity();

        if(arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else if(arity == 2)
        {
            Expression          left            = exprTranslator.translateExpr(expr.left, variablesScope);
            Expression          right           = exprTranslator.translateExpr(expr.right, variablesScope);
            BinaryExpression    product         = new BinaryExpression(right, BinaryExpression.Op.PRODUCT, exprTranslator.translator.universe);

            BinaryExpression    intersection    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, product);

            return intersection;
        }

        throw new UnsupportedOperationException();
    }
    private Expression translateComparison(ExprBinary expr, BinaryExpression.Op op, Map<String,ConstantExpression> variablesScope)
    {

        if
            (   (expr.left instanceof ExprUnary &&
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
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration)
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration)
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }

        if(op == BinaryExpression.Op.NEQ)
        {
            return new UnaryExpression(UnaryExpression.Op.NOT,new BinaryExpression(left, BinaryExpression.Op.EQ, right));
        }
        else
        {
            return new BinaryExpression(left, op, right);
        }
    }

    private Expression translateCardinality(ExprBinary expr, BinaryExpression.Op op , Map<String, ConstantExpression> variablesScope)
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
            Expression  equality = translateCardinalityComparison((ExprUnary) expr.left, n, op, variablesScope);
            return equality;
        }

        if
            (   (expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
            )
        {
            int         n           = ((ExprConstant)expr.left).num;
            Expression  equality = translateCardinalityComparison((ExprUnary) expr.right, n, op, variablesScope);
            return equality;
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateCardinalityComparison(ExprUnary expr, int n, BinaryExpression.Op op ,Map<String, ConstantExpression> variablesScope)
    {
        Expression          left        = exprTranslator.translateExpr(expr.sub, variablesScope);
        FunctionDeclaration declaration =  TranslatorUtils.generateAuxiliarySetNAtoms(expr.sub.type().arity(), n, exprTranslator.translator);
        Expression          right       = declaration.getConstantExpr();
        switch (op)
        {
            case EQ : return new BinaryExpression(left, BinaryExpression.Op.EQ, right);
            case NEQ: return new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(left, BinaryExpression.Op.EQ, right));
            case LTE: return new BinaryExpression(left, BinaryExpression.Op.SUBSET, right);
            case LT :
            {
                Expression lte      = new BinaryExpression(left, BinaryExpression.Op.SUBSET, right);
                Expression notEqual = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(left, BinaryExpression.Op.EQ, right));
                return new BinaryExpression(lte, BinaryExpression.Op.AND, notEqual);
            }
            case GTE: return new BinaryExpression(right, BinaryExpression.Op.SUBSET, left);
            case GT :
            {
                Expression gte      = new BinaryExpression(right, BinaryExpression.Op.SUBSET, left);
                Expression notEqual = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(left, BinaryExpression.Op.EQ, right));
                return new BinaryExpression(gte, BinaryExpression.Op.AND, notEqual);
            }

            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expression translateSetOperation(ExprBinary expr, BinaryExpression.Op op, Map<String, ConstantExpression> variablesScope)
    {
        Expression left     = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression right    = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration)
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration)
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }

        BinaryExpression operation = new BinaryExpression(left, op, right);
        return operation;
    }

    private Expression translateJoin(ExprBinary expr, Map<String, ConstantExpression> variablesScope)
    {
        Expression          left    = exprTranslator.translateExpr(expr.left, variablesScope);
        Expression          right   = exprTranslator.translateExpr(expr.right, variablesScope);

        if(left instanceof ConstantExpression &&
                ((ConstantExpression)left).getDeclaration() instanceof BoundVariableDeclaration)
        {
            left = exprTranslator.getSingleton((ConstantExpression) left);
        }
        if(right instanceof ConstantExpression &&
                ((ConstantExpression)right).getDeclaration() instanceof BoundVariableDeclaration)
        {
            right = exprTranslator.getSingleton((ConstantExpression) right);
        }
        BinaryExpression    join    = new BinaryExpression(left, BinaryExpression.Op.JOIN, right);
        return join;
    }
}
