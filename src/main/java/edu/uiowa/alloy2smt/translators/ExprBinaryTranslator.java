package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprBinary;
import edu.uiowa.alloy2smt.smtAst.BinaryExpression;
import edu.uiowa.alloy2smt.smtAst.BoundVariableDeclaration;
import edu.uiowa.alloy2smt.smtAst.ConstantExpression;
import edu.uiowa.alloy2smt.smtAst.Expression;

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
            case EQUALS             : throw new UnsupportedOperationException();
            case NOT_EQUALS         : throw new UnsupportedOperationException();
            case IMPLIES            : throw new UnsupportedOperationException();
            case LT                 : throw new UnsupportedOperationException();
            case LTE                : throw new UnsupportedOperationException();
            case GT                 : throw new UnsupportedOperationException();
            case GTE                : throw new UnsupportedOperationException();
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
