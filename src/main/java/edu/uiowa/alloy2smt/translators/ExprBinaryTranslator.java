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
            case ARROW              : throw new UnsupportedOperationException();
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
            case DOMAIN             : throw new UnsupportedOperationException();
            case RANGE              : throw new UnsupportedOperationException();
            case INTERSECT          : throw new UnsupportedOperationException();
            case PLUSPLUS           : throw new UnsupportedOperationException();
            case PLUS               : return translatePlus(expr, variablesScope);
            case IPLUS              : throw new UnsupportedOperationException();
            case MINUS              : throw new UnsupportedOperationException();
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
            case IN                 : throw new UnsupportedOperationException();
            case NOT_IN             : throw new UnsupportedOperationException();
            case AND                : throw new UnsupportedOperationException();
            case OR                 : throw new UnsupportedOperationException();
            case IFF                : throw new UnsupportedOperationException();
            default                 : throw new UnsupportedOperationException();
        }
    }

    private Expression translateComparison(ExprBinary expr, BinaryExpression.Op op, Map<String,ConstantExpression> variablesScope)
    {
        Expression equality1 = translateCardinality(expr, op, variablesScope);
        if (equality1 != null) return equality1;

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

        BinaryExpression equality = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
        return equality;
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
        //ToDo: For cardinality operator, CVC4 supports only comparison with numbers

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


        return null;
    }

    private Expression translateCardinalityComparison(ExprUnary expr, int n, BinaryExpression.Op op ,Map<String, ConstantExpression> variablesScope)
    {
        Expression          left        = exprTranslator.translateExpr(expr.sub, variablesScope);
        FunctionDeclaration declaration =  TranslatorUtils.generateAuxiliarySetNAtoms(exprTranslator.translator.setOfUnaryAtomSort, n, exprTranslator.translator);
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
            case GTE: return new BinaryExpression(right, BinaryExpression.Op.LTE, left);
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

    private Expression translateCardinalityComparison(BinaryExpression.Op eq, Expression left, Expression right)
    {
        throw new UnsupportedOperationException();
    }

    private Expression translatePlus(ExprBinary expr, Map<String, ConstantExpression> variablesScope)
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

        BinaryExpression union = new BinaryExpression(left, BinaryExpression.Op.UNION, right);
        return union;
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
