package edu.uiowa.smt.optimizer;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.smtAst.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class SmtOptimizerTests
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
    }

    @Test
    public void unusedUninterpretedInt()
    {
        script.addFunctions(SmtOptimizer.getUninterpretedIntFunctions(script));

        script = SmtOptimizer.optimize(script);

        // all trivial assertions should be filtered out.
        assertTrue(script.getFunctions().isEmpty());
    }

    @Test
    public void empty() throws Exception
    {
        String alloy =  "";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    public void command() throws Exception
    {
        String alloy =  "run {some x: Int | x = 2}";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
    }
}