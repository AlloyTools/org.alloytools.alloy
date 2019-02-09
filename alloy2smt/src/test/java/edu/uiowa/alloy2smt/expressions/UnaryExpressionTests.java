package edu.uiowa.alloy2smt.expressions;

import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class UnaryExpressionTests
{
    Expression booleanConstant = new BooleanConstant(true);
    @Test
    void booleanConstant() throws Exception
    {
        Assertions.assertEquals(Alloy2SmtTranslator.boolSort, booleanConstant.getSort());
    }

    @Test
    void intConstant() throws Exception
    {
        Expression expression = new IntConstant(5);
        Assertions.assertEquals(Alloy2SmtTranslator.intSort, expression.getSort());
    }

    @Test
    void atomConstant() throws Exception
    {
        Expression expression = new AtomConstant("a");
        Assertions.assertEquals(Alloy2SmtTranslator.atomSort, expression.getSort());
    }

    @Test
    void or() throws Exception
    {
        Expression expression = new BinaryExpression(booleanConstant, BinaryExpression.Op.AND, booleanConstant);
        Assertions.assertEquals(Alloy2SmtTranslator.boolSort, expression.getSort());
    }
}
