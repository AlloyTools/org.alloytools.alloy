package edu.uiowa.alloy2smt.expressions;

import edu.uiowa.alloy2smt.smt.smtAst.*;
import edu.uiowa.alloy2smt.smt.AbstractTranslator;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class UnaryExpressionTests
{
    Expression booleanConstant = new BoolConstant(true);
    @Test
    void booleanConstant()
    {
        Assertions.assertEquals(AbstractTranslator.boolSort, booleanConstant.getSort());
    }

    @Test
    void intConstant()
    {
        Expression expression = IntConstant.getInstance(5);
        Assertions.assertEquals(AbstractTranslator.intSort, expression.getSort());
    }

    @Test
    void atomConstant()
    {
        Expression expression = new UninterpretedConstant("a", AbstractTranslator.atomSort);
        Assertions.assertEquals(AbstractTranslator.atomSort, expression.getSort());
    }

    @Test
    void or()
    {
        Expression expression = new BinaryExpression(booleanConstant, BinaryExpression.Op.AND, booleanConstant);
        Assertions.assertEquals(AbstractTranslator.boolSort, expression.getSort());
    }
}
