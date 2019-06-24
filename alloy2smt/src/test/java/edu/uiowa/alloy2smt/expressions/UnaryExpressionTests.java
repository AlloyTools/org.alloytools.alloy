package edu.uiowa.alloy2smt.expressions;

import edu.uiowa.smt.smtAst.*;
import edu.uiowa.smt.AbstractTranslator;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class UnaryExpressionTests
{
    Expression booleanConstant = BoolConstant.True;
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
        Expression expression = BinaryExpression.Op.AND.make(booleanConstant, booleanConstant);
        Assertions.assertEquals(AbstractTranslator.boolSort, expression.getSort());
    }
}
