package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SmtRewriter implements ISmtRewriter
{
  @Override
  public SmtRewriteResult visit(SmtAst smtAst)
  {
    if (smtAst instanceof Assertion)
    {
      return visit((Assertion) smtAst);
    }
    else if (smtAst instanceof Declaration)
    {
      return visit((Declaration) smtAst);
    }
    else if (smtAst instanceof ExpressionValue)
    {
      return visit((ExpressionValue) smtAst);
    }
    else if (smtAst instanceof SmtExpr)
    {
      return visit((SmtExpr) smtAst);
    }
    else if (smtAst instanceof SmtScript)
    {
      return visit((SmtScript) smtAst);
    }
    else if (smtAst instanceof SmtModel)
    {
      return visit((SmtModel) smtAst);
    }
    else if (smtAst instanceof SmtSettings)
    {
      return visit((SmtSettings) smtAst);
    }
    else if (smtAst instanceof SmtUnsatCore)
    {
      return visit((SmtUnsatCore) smtAst);
    }
    else if (smtAst instanceof SmtValues)
    {
      return visit((SmtValues) smtAst);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public SmtRewriteResult visit(Declaration declaration)
  {
    if (declaration instanceof FunctionDefinition)
    {
      return visit((FunctionDefinition) declaration);
    }
    else if (declaration instanceof FunctionDeclaration)
    {
      return visit((FunctionDeclaration) declaration);
    }
    else if (declaration instanceof SmtVariable)
    {
      return visit((SmtVariable) declaration);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public SmtRewriteResult visit(SmtModel model)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtScript root)
  {
    SmtScript optimizedScript = new SmtScript(root);
    optimizedScript = optimizeHelper (root, optimizedScript);
    return SmtRewriteResult.Status.Done.make(optimizedScript);
  }

  public SmtScript optimizeHelper(SmtScript root, SmtScript optimizedScript)
  {
    optimizedScript = visitAssertions(optimizedScript);
    optimizedScript = removeTrivialAssertions(optimizedScript);
    optimizedScript = removeUninterpretedIntIfNotUsed(root, optimizedScript);
    List<SmtScript> children = new ArrayList<>(optimizedScript.getChildren());
    optimizedScript.clearChildren();
    // optimize children as well
    for (SmtScript child : children)
    {
      SmtScript optimizedChild = optimizeHelper(root, child);
      optimizedScript.addChild(optimizedChild);
    }
    return optimizedScript;
  }

  private SmtScript removeTrivialAssertions(SmtScript script)
  {
    List<Assertion> assertions = script.getAssertions()
                                       .stream()
                                       .filter(a -> !isTrivial(a))
                                       .collect(Collectors.toList());
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


  public SmtScript removeUninterpretedIntIfNotUsed(SmtScript root, SmtScript script)
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

  private SmtScript visitAssertions(SmtScript script)
  {
    List<Assertion> assertions = new ArrayList<>();

    for (Assertion assertion : script.getAssertions())
    {
      assertions.add((Assertion) (visit(assertion)).smtAst);
    }

    script.setAssertions(assertions);
    return script;
  }

  private SmtRewriteResult optimizedTupleSelectZeroForUnaryTuples(SmtLetExpr letExpr)
  {
    // Original : (let ((x (mkTuple a))) (= ((_ tupSel 0) x) 5))
    // Optimized: (let ((x (mkTuple a))) (= (a 5))

    SmtExpr zero = new IntConstant("0");

    SmtRewriteResult bodyResult = visit(letExpr.getSmtExpr());
    SmtExpr optimizedBody = (SmtExpr) bodyResult.smtAst;
    for (Map.Entry<SmtVariable, SmtExpr> entry : letExpr.getLetVariables().entrySet())
    {
      SmtVariable smtVariable = entry.getKey();
      SmtExpr expr = entry.getValue();

      // check if the tuple has arity 1
      if (expr instanceof SmtMultiArityExpr &&
          ((SmtMultiArityExpr) expr).getOp() == SmtMultiArityExpr.Op.MKTUPLE &&
          ((SmtMultiArityExpr) expr).getExpressions().size() == 1)
      {
        SmtMultiArityExpr makeTuple = (SmtMultiArityExpr) expr;
        SmtExpr tupleSelect = SmtBinaryExpr.Op.TUPSEL.make(zero, smtVariable.getVariable());
        optimizedBody = optimizedBody.replace(tupleSelect, makeTuple.get(0));
      }
    }

    SmtExpr optimizedLet = new SmtLetExpr(letExpr.getLetVariables(), optimizedBody);
    return bodyResult.status.make(optimizedLet);
  }

  @Override
  public SmtRewriteResult visit(SmtBinaryExpr expr)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(Sort sort)
  {
    if (sort instanceof UninterpretedSort)
    {
      return visit((UninterpretedSort) sort);
    }
    else if (sort instanceof SetSort)
    {
      return visit((SetSort) sort);
    }
    else if (sort instanceof TupleSort)
    {
      return visit((TupleSort) sort);
    }
    else if (sort instanceof IntSort)
    {
      return visit((IntSort) sort);
    }
    else if (sort instanceof RealSort)
    {
      return visit((RealSort) sort);
    }
    else if (sort instanceof StringSort)
    {
      return visit((StringSort) sort);
    }
    else if (sort instanceof BoolSort)
    {
      return visit((BoolSort) sort);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public SmtRewriteResult visit(IntSort intSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtQtExpr quantifiedExpression)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(RealSort realSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SetSort setSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(StringSort stringSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(TupleSort tupleSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtExpr smtExpr)
  {
    SmtRewriteResult rewriteResult;
    if (smtExpr instanceof Variable)
    {
      rewriteResult = visit((Variable) smtExpr);
    }
    else if (smtExpr instanceof SmtUnaryExpr)
    {
      rewriteResult = visit((SmtUnaryExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtBinaryExpr)
    {
      rewriteResult = visit((SmtBinaryExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtMultiArityExpr)
    {
      rewriteResult = visit((SmtMultiArityExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtQtExpr)
    {
      rewriteResult = visit((SmtQtExpr) smtExpr);
    }
    else if (smtExpr instanceof Sort)
    {
      rewriteResult = visit((Sort) smtExpr);
    }
    else if (smtExpr instanceof IntConstant)
    {
      rewriteResult = visit((IntConstant) smtExpr);
    }
    else if (smtExpr instanceof SmtCallExpr)
    {
      rewriteResult = visit((SmtCallExpr) smtExpr);
    }
    else if (smtExpr instanceof BoolConstant)
    {
      rewriteResult = visit((BoolConstant) smtExpr);
    }
    else if (smtExpr instanceof SmtLetExpr)
    {
      rewriteResult = visit((SmtLetExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtIteExpr)
    {
      rewriteResult = visit((SmtIteExpr) smtExpr);
    }
    else if (smtExpr instanceof UninterpretedConstant)
    {
      rewriteResult = visit((UninterpretedConstant) smtExpr);
    }
    else
    {
      throw new UnsupportedOperationException();
    }

    if (rewriteResult.status == SmtRewriteResult.Status.Done)
    {
      return rewriteResult;
    }

    return visit((SmtExpr) rewriteResult.smtAst);
  }

  @Override
  public SmtRewriteResult visit(SmtUnaryExpr unaryExpression)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(UninterpretedSort uninterpretedSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(IntConstant intConstant)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(Variable variable)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(FunctionDeclaration functionDeclaration)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(FunctionDefinition functionDefinition)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(BoolConstant booleanConstant)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(Assertion assertion)
  {
    SmtRewriteResult result = visit(assertion.getSmtExpr());

    Assertion optimizedAssertion = new Assertion(assertion.getSymbolicName(), assertion.getComment(), (SmtExpr) result.smtAst);
    return SmtRewriteResult.Status.Done.make(optimizedAssertion);
  }

  @Override
  public SmtRewriteResult visit(SmtMultiArityExpr expression)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtCallExpr smtCallExpr)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtVariable smtVariable)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(BoolSort boolSort)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtLetExpr smtLetExpr)
  {
    return optimizedTupleSelectZeroForUnaryTuples(smtLetExpr);
  }

  @Override
  public SmtRewriteResult visit(SmtIteExpr iteExpression)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(UninterpretedConstant uninterpretedConstant)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtSettings smtSettings)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtValues smtValues)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(ExpressionValue expressionValue)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public SmtRewriteResult visit(SmtUnsatCore smtUnsatCore)
  {
    throw new UnsupportedOperationException();
  }
}
