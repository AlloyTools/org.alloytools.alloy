package edu.uiowa.alloy2smt.expressions;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.BoolSort;
import edu.uiowa.alloy2smt.smtAst.BooleanConstant;
import edu.uiowa.alloy2smt.smtAst.Expression;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import edu.uiowa.alloy2smt.translators.Translation;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class UnaryExpressionTests
{
    @Test
    void booleanConstant()
    {
        Expression expression = new BooleanConstant(true);
        Assertions.assertTrue(expression.getSort() instanceof  BoolSort);
    }
}
