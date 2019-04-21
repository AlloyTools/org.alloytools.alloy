package edu.uiowa.alloy2smt.expressions;

import edu.uiowa.alloy2smt.smt.smtAst.*;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class UnaryExpressionTests
{
    Expression booleanConstant = new BoolConstant(true);
    @Test
    void booleanConstant()
    {
        Assertions.assertEquals(Alloy2SmtTranslator.boolSort, booleanConstant.getSort());
    }

    @Test
    void intConstant()
    {
        Expression expression = IntConstant.getInstance(5);
        Assertions.assertEquals(Alloy2SmtTranslator.intSort, expression.getSort());
    }

    @Test
    void atomConstant()
    {
        Expression expression = new UninterpretedConstant("a", Alloy2SmtTranslator.atomSort);
        Assertions.assertEquals(Alloy2SmtTranslator.atomSort, expression.getSort());
    }

    @Test
    void or()
    {
        Expression expression = new BinaryExpression(booleanConstant, BinaryExpression.Op.AND, booleanConstant);
        Assertions.assertEquals(Alloy2SmtTranslator.boolSort, expression.getSort());
    }
}
