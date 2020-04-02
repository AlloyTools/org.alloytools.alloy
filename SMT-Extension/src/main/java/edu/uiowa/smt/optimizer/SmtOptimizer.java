package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.smtAst.*;

import java.util.List;
import java.util.stream.Collectors;

public class SmtOptimizer
{
    private static SmtScript root;
    public static SmtScript optimize(SmtScript smtScript)
    {
        root = smtScript;
        return optimizeHelper(root);
    }
    public static SmtScript optimizeHelper(SmtScript script)
    {
        SmtScript optimizedScript = new SmtScript(script);
        optimizedScript = removeTrivialAssertions(optimizedScript);
        optimizedScript = removeUninterpretedIntIfNotUsed(optimizedScript);

        // optimize children as well
        for (SmtScript child :script.getChildren())
        {
            SmtScript optimizedChild = optimizeHelper(child);
            optimizedScript.addChild(optimizedChild);
        }
        return optimizedScript;
    }

    private static SmtScript removeTrivialAssertions(SmtScript script)
    {
        List<Assertion> assertions = script.getAssertions()
                                           .stream().filter(a -> !isTrivial(a)).collect(Collectors.toList());
        script.setAssertions(assertions);
        return script;
    }

    public static boolean isTrivial(Assertion assertion)
    {
        Expression expr = assertion.getExpression();

        // (assert true)
        if (expr.equals(BoolConstant.True))
        {
            return true;
        }

        if (expr instanceof MultiArityExpression)
        {
            MultiArityExpression smtMultiArity = (MultiArityExpression) expr;
            if (smtMultiArity.getOp() == MultiArityExpression.Op.AND)
            {
                // (assert (and))
                if (smtMultiArity.getExpressions().isEmpty())
                {
                    return true;
                }
                // (assert (and true))
                if (smtMultiArity.getExpressions().size() == 1 && smtMultiArity.get(0).equals(BoolConstant.True))
                {
                    return true;
                }
            }

            if (smtMultiArity.getOp() == MultiArityExpression.Op.OR)
            {
                // (assert (or true))
                if (smtMultiArity.getExpressions().size() == 1 && smtMultiArity.get(0).equals(BoolConstant.True))
                {
                    return true;
                }
            }
        }
        return false;
    }

    public static SmtScript removeUninterpretedIntIfNotUsed(SmtScript script)
    {
        if (!root.isUninterpretedIntUsed())
        {
            script.removeSort(AbstractTranslator.uninterpretedInt);

            List<FunctionDeclaration> uIntFunctions = AbstractTranslator.getUninterpretedIntFunctions(script);
            script.removeFunctions(uIntFunctions);

            List<Assertion> uIntAssertions = AbstractTranslator.getUninterpretedIntAssertions(script);
            script.removeAssertions(uIntAssertions);
        }
        return script;
    }
}
