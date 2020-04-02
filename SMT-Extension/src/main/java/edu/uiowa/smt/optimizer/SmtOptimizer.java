package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class SmtOptimizer
{
    public static SmtScript optimize(SmtScript script)
    {
        SmtScript optimizedScript = new SmtScript(script);
        optimizedScript = removeTrivialAssertions(optimizedScript);
        optimizedScript = removeUinterpretedIntIfNotUsed(optimizedScript);
        return optimizedScript;
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

    private static SmtScript removeUinterpretedIntIfNotUsed(SmtScript script)
    {
        if (!isUIntUsed(script))
        {
            script.removeSort(AbstractTranslator.uninterpretedInt);

            List<FunctionDeclaration> uIntFunctions = getUninterpretedIntFunctions(script);
            script.removeFunctions(uIntFunctions);

            List<Assertion> uIntAssertions = getUninterpretedIntAssertions(script);
            script.removeAssertions(uIntAssertions);
        }

        return script;
    }

    public static List<FunctionDeclaration> getUninterpretedIntFunctions(SmtScript script)
    {
        List<FunctionDeclaration> functions = new ArrayList<>(Arrays.asList(AbstractTranslator.uninterpretedIntValue, AbstractTranslator.idenInt, AbstractTranslator.univInt));

        //ToDo: delete when alloy parser supports univInt
        List<FunctionDeclaration> univInt = script.getFunctions().stream()
                                             .filter(f -> f.getName().equals("integer/univInt"))
                                             .collect(Collectors.toList());
        functions.addAll(univInt);
        return functions;
    }

    private static List<Assertion> getUninterpretedIntAssertions(SmtScript script)
    {
        List<Assertion> assertions = new ArrayList<>();
        assertions.add(AbstractTranslator.univIntAssertion);
        assertions.add(AbstractTranslator.idenIntAssertion);
        assertions.add(AbstractTranslator.intValueAssertion);

        //ToDo: remove this when alloy parser supports univInt and idenInt
        List<Assertion> alloyUnivInt = script.getAssertions().stream()
                                             .filter(a -> a.getComment().equals("integer/univInt = Int"))
                                             .collect(Collectors.toList());

        List<Assertion> alloyIdenInt = script.getAssertions().stream()
                                             .filter(a -> a.getComment().equals("(all x,y | x = y <=> x -> y in (integer/univInt <: idenInt))"))
                                             .collect(Collectors.toList());

        assertions.addAll(alloyUnivInt);
        assertions.addAll(alloyIdenInt);

        return assertions;
    }

    private static boolean isUIntUsed(SmtScript script)
    {
        List<FunctionDeclaration> excludedFunctions = getUninterpretedIntFunctions(script);
        for (FunctionDeclaration function : script.getFunctions())
        {
            if (excludedFunctions.contains(function))
            {
                // skip default functions for uninterpreted integers
                continue;
            }

            UninterpretedIntVisitor visitor = new UninterpretedIntVisitor();
            visitor.visit(function);
            if (visitor.isUninterpretedIntUsed())
            {
                return true;
            }

        }

        List<Assertion> excludedAssertions = getUninterpretedIntAssertions(script);

        for (Assertion assertion : script.getAssertions())
        {
            if (excludedAssertions.contains(assertion))
            {
                // skip default assertions for uninterpreted integers
                continue;
            }

            UninterpretedIntVisitor visitor = new UninterpretedIntVisitor();
            visitor.visit(assertion);
            if (visitor.isUninterpretedIntUsed())
            {
                return true;
            }
        }
        return false;
    }
}
