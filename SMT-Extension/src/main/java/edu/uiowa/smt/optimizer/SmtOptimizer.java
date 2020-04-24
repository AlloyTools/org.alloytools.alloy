package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
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

    optimizedScript = optimizeSmtExpr(optimizedScript);


    // optimize children as well
    for (SmtScript child : script.getChildren())
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
    SmtExpr expr = assertion.getSmtExpr();

    // (assert true)
    if (expr.equals(BoolConstant.True))
    {
      return true;
    }

    if (expr instanceof SmtMultiArityExpr)
    {
      SmtMultiArityExpr smtMultiArity = (SmtMultiArityExpr) expr;
      if (smtMultiArity.getOp() == SmtMultiArityExpr.Op.AND)
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

      if (smtMultiArity.getOp() == SmtMultiArityExpr.Op.OR)
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

  private static SmtScript optimizeSmtExpr(SmtScript script)
  {
    List<Assertion> assertions = new ArrayList<>();

    for (Assertion assertion: script.getAssertions())
    {
      SmtExpr optimizedExpr = null;
      while(optimizedExpr != assertion.getSmtExpr())
      {
        optimizedExpr = optimizeExpr(assertion.getSmtExpr());
      }
      Assertion optimizedAssertion = new Assertion(assertion.getSymbolicName(), assertion.getComment(), optimizedExpr);
      assertions.add(optimizedAssertion);
    }

    script.setAssertions(assertions);
    return script;
  }

  public static SmtExpr optimizeExpr(SmtExpr smtExpr)
  {
    SmtExpr optimizedExpr;
    optimizedExpr =  optimizedTupleSelectZeroForUnaryTuples(smtExpr);
    return optimizedExpr;
  }

  private static SmtExpr optimizedTupleSelectZeroForUnaryTuples(SmtExpr smtExpr)
  {
    // Original : (let ((x (mkTuple a))) (= ((_ tupSel 0) x) 5))
    // Optimized: (let ((x (mkTuple a))) (= (a 5))

    SmtExpr optimizedExpr = smtExpr;
    if(smtExpr instanceof SmtLetExpr)
    {
      SmtLetExpr letExpr = (SmtLetExpr) smtExpr;
      SmtExpr optimizedBody = letExpr.getSmtExpr();
      for (Map.Entry<SmtVariable, SmtExpr> entry: letExpr.getLetVariables().entrySet())
      {
        SmtVariable smtVariable = entry.getKey();
        SmtExpr expr = entry.getValue();

        // check if the tuple has arity 1
        if(expr instanceof SmtMultiArityExpr &&
            ((SmtMultiArityExpr) expr).getOp() == SmtMultiArityExpr.Op.MKTUPLE &&
            ((SmtMultiArityExpr) expr).getExpressions().size() == 1)
        {
          SmtMultiArityExpr makeTuple = (SmtMultiArityExpr) expr;
          SmtExpr zero = new IntConstant("0");
          SmtExpr tupleSelect = SmtBinaryExpr.Op.TUPSEL.make(zero, smtVariable.getVariable());
          optimizedBody = optimizedBody.replace(tupleSelect, makeTuple.get(0));
        }
      }
      optimizedExpr = new SmtLetExpr(letExpr.getLetVariables(), optimizedBody);
    }

    return optimizedExpr;
  }
}
