package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.smtAst.*;

import java.util.List;
import java.util.stream.Collectors;

public class SmtOptimizer
{
    public static SmtScript optimize(SmtScript script)
    {
        SmtScript script0 = new SmtScript(script);
        SmtScript script1 = removeTrivialAssertions(script0);
        return script1;
    }

    private static SmtScript removeTrivialAssertions(SmtScript script)
    {
        List<Assertion> assertions = script.getAssertions()
                .stream().filter(a -> !isTrivial(a)).collect(Collectors.toList());
        script.setAssertions(assertions);
        return script;
    }

    private static boolean isTrivial(Assertion assertion)
    {
        Expression expr = assertion.getExpression();

        // (assert true)
        if(expr.equals(BoolConstant.True))
        {
            return true;
        }

        if(expr instanceof MultiArityExpression)
        {
            MultiArityExpression smtMultiArity = (MultiArityExpression) expr;
            if(smtMultiArity.getOp() == MultiArityExpression.Op.AND)
            {
                // (assert (and))
                if(smtMultiArity.getExpressions().isEmpty())
                {
                    return true;
                }
                // (assert (and true))
                if(smtMultiArity.getExpressions().size() == 1 && smtMultiArity.get(0).equals(BoolConstant.True))
                {
                    return true;
                }
            }

            if(smtMultiArity.getOp() == MultiArityExpression.Op.OR)
            {
                // (assert (or true))
                if(smtMultiArity.getExpressions().size() == 1 && smtMultiArity.get(0).equals(BoolConstant.True))
                {
                    return true;
                }
            }
        }

        return false;
    }
}
