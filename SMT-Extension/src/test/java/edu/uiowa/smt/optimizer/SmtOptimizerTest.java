package edu.uiowa.smt.optimizer;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.smtAst.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class SmtOptimizerTest
{
    private SmtScript script = new SmtScript();

    @BeforeEach
    private void reset()
    {
        script.reset();
    }

    @Test
    public void trivialAssertions()
    {
        script.addAssertion(new Assertion("", "", BoolConstant.True));
        Expression andTrue = MultiArityExpression.Op.AND.make(BoolConstant.True);
        script.addAssertion(new Assertion("", "", andTrue));
        Expression orTrue = MultiArityExpression.Op.OR.make(BoolConstant.True);
        script.addAssertion(new Assertion("", "", orTrue));

        script = SmtOptimizer.optimize(script);

        // all trivial assertions should be filtered out.
        assertTrue(script.getAssertions().isEmpty());

        assertEquals(0, script.getAssertions().size());
    }
}