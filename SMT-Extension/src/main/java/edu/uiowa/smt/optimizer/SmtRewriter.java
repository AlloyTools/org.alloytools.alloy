package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
    return SmtRewriteResult.Status.Done.make(model);
  }

  @Override
  public SmtRewriteResult visit(SmtScript root)
  {
    root = optimizeHelper(root, root);
    return SmtRewriteResult.Status.Done.make(root);
  }

  public SmtScript optimizeHelper(SmtScript root, SmtScript optimizedScript)
  {
    optimizedScript = visitFunctionDefinitions(optimizedScript);
    optimizedScript = visitAssertions(optimizedScript);
    optimizedScript = removeTrivialAssertions(optimizedScript);
    optimizedScript = removeUninterpretedIntIfNotUsed(root, optimizedScript);
    List<SmtScript> children = new ArrayList<>();
    children.addAll(optimizedScript.getChildren());
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
                                       .filter(a -> !a.getSmtExpr().equals((BoolConstant.True)))
                                       .collect(Collectors.toList());
    script.setAssertions(assertions);

    return script;
  }

  public SmtRewriteResult removeTrivialTerms(SmtMultiArityExpr smtMultiArity)
  {
    List<SmtExpr> exprs = smtMultiArity.getExprs();
    SmtRewriteResult.Status status = SmtRewriteResult.Status.Done;
    SmtExpr smtAst = smtMultiArity;
    if (smtMultiArity.getOp() == SmtMultiArityExpr.Op.AND)
    {
      exprs = exprs.stream().filter(e -> !e.equals(BoolConstant.True)).collect(Collectors.toList());
      if (exprs.size() != smtMultiArity.getExprs().size())
      {
        status = SmtRewriteResult.Status.RewriteAgain;
        // (and)
        if (exprs.isEmpty())
        {
          smtAst = BoolConstant.True;
        }
        else if (exprs.size() == 1)
        {
          smtAst = exprs.get(0);
        }
        else
        {
          smtAst = SmtMultiArityExpr.Op.AND.make(exprs);
        }
      }
    }
    if (smtMultiArity.getOp() == SmtMultiArityExpr.Op.OR)
    {
      //(or true ...)
      if (exprs.contains(BoolConstant.True))
      {
        smtAst = BoolConstant.True;
        status = SmtRewriteResult.Status.RewriteAgain;
      }
    }

    return status.make(smtAst);
  }

  public SmtRewriteResult flattenNestedExprs(SmtMultiArityExpr smtMultiArity, SmtRewriteResult.Status status)
  {
    SmtExpr smtAst = smtMultiArity;
    if (smtMultiArity.getOp() == SmtMultiArityExpr.Op.AND ||
        smtMultiArity.getOp() == SmtMultiArityExpr.Op.OR)
    {
      // Original: (and (and p q) ... )
      // Optimized: (and p q ...)
      List<SmtExpr> exprs = new ArrayList<>();
      for (SmtExpr expr : smtMultiArity.getExprs())
      {
        if (expr instanceof SmtMultiArityExpr &&
            ((SmtMultiArityExpr) expr).getOp() == smtMultiArity.getOp())
        {
          exprs.addAll(((SmtMultiArityExpr) expr).getExprs());
          status = SmtRewriteResult.Status.RewriteAgain;
        }
        else
        {
          exprs.add(expr);
        }
      }
      smtAst = smtMultiArity.getOp().make(exprs);
    }
    return status.make(smtAst);
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

  private SmtScript visitFunctionDefinitions(SmtScript script)
  {
    List<FunctionDeclaration> functions = new ArrayList<>();

    for (FunctionDeclaration function : script.getFunctions())
    {
      if (function instanceof FunctionDefinition)
      {
        functions.add((FunctionDefinition) visit((FunctionDefinition) function).smtAst);
      }
      else
      {
        functions.add(function);
      }
    }

    script.setFunctions(functions);
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
          ((SmtMultiArityExpr) expr).getExprs().size() == 1)
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
    SmtRewriteResult resultA = visit(expr.getA());
    SmtRewriteResult resultB = visit(expr.getB());
    SmtExpr smtAst = expr.getOp().make((SmtExpr) resultA.smtAst, (SmtExpr) resultB.smtAst);
    if (resultA.status == SmtRewriteResult.Status.Done ||
        resultB.status == SmtRewriteResult.Status.Done)
    {
      return SmtRewriteResult.Status.Done.make(smtAst);
    }
    else
    {
      return SmtRewriteResult.Status.RewriteAgain.make(smtAst);
    }
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
    return SmtRewriteResult.Status.Done.make(intSort);
  }

  @Override
  public SmtRewriteResult visit(SmtQtExpr smtQtExpr)
  {
    SmtRewriteResult bodyResult = visit(smtQtExpr.getExpr());
    SmtQtExpr smtAst = smtQtExpr.getOp().make((SmtExpr) bodyResult.smtAst, smtQtExpr.getVariables());
    SmtRewriteResult result = optimizeTupleQuantifiers(smtAst);
    if (result.status == SmtRewriteResult.Status.RewriteAgain)
    {
      return result;
    }
    return bodyResult.status.make(result.smtAst);
  }

  public SmtRewriteResult optimizeTupleQuantifiers(SmtQtExpr smtQtExpr)
  {
    List<SmtVariable> declarations = new ArrayList<>();
    Map<SmtVariable, SmtExpr> letVariables = new LinkedHashMap<>();
    for (SmtVariable variable : smtQtExpr.getVariables())
    {
      if (variable.getSort() instanceof TupleSort)
      {
        List<SmtExpr> tupleSmtExprs = new ArrayList<>();
        // convert tuple quantifiers to uninterpreted quantifiers
        TupleSort tupleSort = (TupleSort) variable.getSort();
        for (Sort sort : tupleSort.elementSorts)
        {
          SmtVariable declaration = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
          declarations.add(declaration);
          tupleSmtExprs.add(declaration.getVariable());
        }
        SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(tupleSmtExprs);
        letVariables.put(variable, tuple);
      }
      else
      {
        declarations.add(variable);
      }
    }
    if (letVariables.size() > 0)
    {
      SmtExpr let = new SmtLetExpr(letVariables, smtQtExpr.getExpr());
      SmtExpr smtAst = smtQtExpr.getOp().make(let, declarations);
      return SmtRewriteResult.Status.RewriteAgain.make(smtAst);
    }
    else
    {
      return SmtRewriteResult.Status.Done.make(smtQtExpr);
    }
  }

  @Override
  public SmtRewriteResult visit(RealSort realSort)
  {
    return SmtRewriteResult.Status.Done.make(realSort);
  }

  @Override
  public SmtRewriteResult visit(SetSort setSort)
  {
    return SmtRewriteResult.Status.Done.make(setSort);
  }

  @Override
  public SmtRewriteResult visit(StringSort stringSort)
  {
    return SmtRewriteResult.Status.Done.make(stringSort);
  }

  @Override
  public SmtRewriteResult visit(TupleSort tupleSort)
  {
    return SmtRewriteResult.Status.Done.make(tupleSort);
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
  public SmtRewriteResult visit(SmtUnaryExpr expr)
  {
    SmtRewriteResult result = visit(expr.getExpr());

    SmtExpr smtAst = expr.getOp().make((SmtExpr) result.smtAst);
    return result.status.make(smtAst);
  }

  @Override
  public SmtRewriteResult visit(UninterpretedSort uninterpretedSort)
  {
    return SmtRewriteResult.Status.Done.make(uninterpretedSort);
  }

  @Override
  public SmtRewriteResult visit(IntConstant intConstant)
  {
    return SmtRewriteResult.Status.Done.make(intConstant);
  }

  @Override
  public SmtRewriteResult visit(Variable variable)
  {
    return SmtRewriteResult.Status.Done.make(variable);
  }

  @Override
  public SmtRewriteResult visit(FunctionDeclaration functionDeclaration)
  {
    return SmtRewriteResult.Status.Done.make(functionDeclaration);
  }

  @Override
  public SmtRewriteResult visit(FunctionDefinition functionDefinition)
  {
    SmtRewriteResult bodyResult = visit(functionDefinition.getBody());
    functionDefinition.setBody((SmtExpr) bodyResult.smtAst);
    return SmtRewriteResult.Status.Done.make(functionDefinition);
  }

  @Override
  public SmtRewriteResult visit(BoolConstant booleanConstant)
  {
    return SmtRewriteResult.Status.Done.make(booleanConstant);
  }

  @Override
  public SmtRewriteResult visit(Assertion assertion)
  {
    SmtRewriteResult result = visit(assertion.getSmtExpr());
    SmtExpr smtExpr = optimizeFunctionalRelation((SmtExpr) result.smtAst);
    smtExpr = optimizeProductMultiplicity(smtExpr);
    smtExpr = optimizeOneArrowAnyMultiplicity(smtExpr);
    smtExpr = optimizeAnyArrowOneMultiplicity(smtExpr);
    Assertion optimizedAssertion = new Assertion(assertion.getSymbolicName(), assertion.getComment(), smtExpr);
    return SmtRewriteResult.Status.Done.make(optimizedAssertion);
  }

  private SmtExpr optimizeFunctionalRelation(SmtExpr expr)
  {
    // change multiplicity translation for one-to-one binary function f: A -> B
    // original:
    // ---------
    // (forall ((a Atom))
    //   (let ((t (mkTuple a)))
    //     (=>
    //       (member t A)
    //       (let ((s (join (singleton t) f)))
    //         (and
    //          (member (choose s) B)
    //          (= (singleton (choose s)) s)
    //
    // optimized:
    // ---------
    // (and
    //   (forall ((x Atom) (y Atom) (z Atom))
    //       (=>
    //         (and (member (mkTuple x y) f) (not (= y z)))
    //         (not (member (mkTuple x z) f))
    //
    //   (forall ((x Atom))
    //     (=>
    //       (member (mkTuple x) A)
    //       (exists ((y Atom))
    //         (and
    //            (member (mkTuple y) B
    //            (member (mkTuple x y) f)
    //       )

    if (!(expr instanceof SmtQtExpr))
    {
      return expr;
    }

    SmtQtExpr smtQtExpr = (SmtQtExpr) expr;
    if (smtQtExpr.getOp() != SmtQtExpr.Op.FORALL || smtQtExpr.getVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr a = smtQtExpr.getVariables().get(0).getVariable();
    SmtExpr aTuple = SmtMultiArityExpr.Op.MKTUPLE.make(a);
    if (!(smtQtExpr.getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let1 = (SmtLetExpr) smtQtExpr.getExpr();
    if (let1.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr t = let1.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr tExpr = let1.getLetVariables().values().stream().findFirst().get();
    if (!tExpr.equals(aTuple))
    {
      return expr;
    }
    if (!(let1.getSmtExpr() instanceof SmtBinaryExpr))
    {
      return expr;
    }
    SmtBinaryExpr implies = (SmtBinaryExpr) let1.getSmtExpr();
    if (implies.getOp() != SmtBinaryExpr.Op.IMPLIES)
    {
      return expr;
    }
    if (!(implies.getA() instanceof SmtBinaryExpr && implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtBinaryExpr operand1 = (SmtBinaryExpr) implies.getA();
    if (!(operand1.getOp() == SmtBinaryExpr.Op.MEMBER && operand1.getA().equals(t)))
    {
      return expr;
    }
    SmtExpr setA = operand1.getB();
    if (!(implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let2 = (SmtLetExpr) implies.getB();
    if (let2.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr s = let2.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr sExpr = let2.getLetVariables().values().stream().findFirst().get();
    if (!(sExpr instanceof SmtBinaryExpr))
    {
      return sExpr;
    }
    SmtExpr f = ((SmtBinaryExpr) sExpr).getB();
    SmtExpr singletonT = SmtUnaryExpr.Op.SINGLETON.make(t);
    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(singletonT, f);
    if (!sExpr.equals(join))
    {
      return expr;
    }

    if (!(let2.getSmtExpr() instanceof SmtMultiArityExpr))
    {
      return expr;
    }

    SmtMultiArityExpr and1 = (SmtMultiArityExpr) let2.getSmtExpr();

    if (!(and1.getOp() == SmtMultiArityExpr.Op.AND && and1.getExprs().size() == 2 &&
        and1.get(0) instanceof SmtBinaryExpr
    ))
    {
      return expr;
    }

    SmtExpr choose = SmtUnaryExpr.Op.CHOOSE.make(s);
    operand1 = (SmtBinaryExpr) and1.get(0);
    if (!(operand1.getOp() == SmtBinaryExpr.Op.MEMBER && operand1.getA().equals(choose)))
    {
      return expr;
    }

    SmtBinaryExpr operand2 = (SmtBinaryExpr) and1.get(1);
    SmtExpr singletonChoose = SmtUnaryExpr.Op.SINGLETON.make(choose);
    SmtExpr equal1 = SmtBinaryExpr.Op.EQ.make(singletonChoose, s);
    if (!operand2.equals(equal1))
    {
      return expr;
    }

    SmtExpr setB = operand1.getB();
    TupleSort tupleSortA = (TupleSort) ((SetSort) setA.getSort()).elementSort;
    TupleSort tupleSortB = (TupleSort) ((SetSort) setB.getSort()).elementSort;
    if (tupleSortA.elementSorts.size() != 1 || tupleSortB.elementSorts.size() != 1)
    {
      return expr;
    }
    Sort elementSortA = tupleSortA.elementSorts.get(0);
    Sort elementSortB = tupleSortB.elementSorts.get(0);

    SmtVariable x = new SmtVariable("x", elementSortA, false);
    SmtVariable y = new SmtVariable("y", elementSortB, false);
    SmtVariable z = new SmtVariable("z", elementSortB, false);

    SmtExpr xTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable());
    SmtExpr yTuple = SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable());
    SmtExpr xyTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), y.getVariable());
    SmtExpr xzTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), z.getVariable());

    SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, f);
    SmtExpr equal = SmtBinaryExpr.Op.EQ.make(y.getVariable(), z.getVariable());
    SmtExpr notEqual = SmtUnaryExpr.Op.NOT.make(equal);
    SmtExpr and2 = SmtMultiArityExpr.Op.AND.make(xyMember, notEqual);
    SmtExpr xzMember = SmtBinaryExpr.Op.MEMBER.make(xzTuple, f);
    SmtExpr xzNotMember = SmtUnaryExpr.Op.NOT.make(xzMember);
    SmtExpr implies2 = SmtBinaryExpr.Op.IMPLIES.make(and2, xzNotMember);
    SmtExpr forall1 = SmtQtExpr.Op.FORALL.make(implies2, x, y, z);

    SmtExpr xMember = SmtBinaryExpr.Op.MEMBER.make(xTuple, setA);
    SmtExpr yMember = SmtBinaryExpr.Op.MEMBER.make(yTuple, setB);
    SmtExpr and3 = SmtMultiArityExpr.Op.AND.make(yMember, xyMember);
    SmtExpr exist = SmtQtExpr.Op.EXISTS.make(and3, y);
    SmtExpr implies3 = SmtBinaryExpr.Op.IMPLIES.make(xMember, exist);

    SmtExpr forall2 = SmtQtExpr.Op.FORALL.make(implies3, x);

    SmtExpr and4 = SmtMultiArityExpr.Op.AND.make(forall1, forall2);
    return and4;
  }

  private SmtExpr optimizeProductMultiplicity(SmtExpr expr)
  {
    // change multiplicity translation for subset relations f: A -> B -> ...
    // original:
    // ---------
    // ; field (A <: g) multiplicity
    //(assert 
    // (forall ((a Atom)) 
    //   (let ((t (mkTuple a))) 
    //     (=> 
    //       (member t |A |) 
    //       (let ( (s (join (singleton t) f ))) ; s = {t} . f 
    //         (subset s (product B (product C D)))))))) ; s : A x B x C x D

    // optimized:
    // ---------
    // (assert true)
    // We return true here because we already generate the assertion below separately
    // ; field f subset
    //(assert (subset f (product A  (product B (product C D))))))

    if (!(expr instanceof SmtQtExpr))
    {
      return expr;
    }

    SmtQtExpr smtQtExpr = (SmtQtExpr) expr;
    if (smtQtExpr.getOp() != SmtQtExpr.Op.FORALL || smtQtExpr.getVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr a = smtQtExpr.getVariables().get(0).getVariable();
    SmtExpr aTuple = SmtMultiArityExpr.Op.MKTUPLE.make(a);
    if (!(smtQtExpr.getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let1 = (SmtLetExpr) smtQtExpr.getExpr();
    if (let1.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr t = let1.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr tExpr = let1.getLetVariables().values().stream().findFirst().get();
    if (!tExpr.equals(aTuple))
    {
      return expr;
    }
    if (!(let1.getSmtExpr() instanceof SmtBinaryExpr))
    {
      return expr;
    }
    SmtBinaryExpr implies = (SmtBinaryExpr) let1.getSmtExpr();
    if (implies.getOp() != SmtBinaryExpr.Op.IMPLIES)
    {
      return expr;
    }
    if (!(implies.getA() instanceof SmtBinaryExpr && implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtBinaryExpr operand1 = (SmtBinaryExpr) implies.getA();
    if (!(operand1.getOp() == SmtBinaryExpr.Op.MEMBER && operand1.getA().equals(t)))
    {
      return expr;
    }
    SmtExpr setA = operand1.getB();
    if (!(implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let2 = (SmtLetExpr) implies.getB();
    if (let2.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr s = let2.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr sExpr = let2.getLetVariables().values().stream().findFirst().get();
    if (!(sExpr instanceof SmtBinaryExpr))
    {
      return sExpr;
    }
    SmtExpr f = ((SmtBinaryExpr) sExpr).getB();
    SmtExpr singletonT = SmtUnaryExpr.Op.SINGLETON.make(t);
    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(singletonT, f);
    if (!sExpr.equals(join))
    {
      return expr;
    }

    if (!(let2.getSmtExpr() instanceof SmtBinaryExpr &&
        ((SmtBinaryExpr) let2.getSmtExpr()).getOp() == SmtBinaryExpr.Op.SUBSET))
    {
      return expr;
    }

    SmtBinaryExpr subset = (SmtBinaryExpr) let2.getSmtExpr();

    if (!(s.equals(subset.getA()) && subset.getB() instanceof SmtBinaryExpr))
    {
      return expr;
    }

    SmtBinaryExpr product = (SmtBinaryExpr) subset.getB();
    if (!isProductExpr(product))
    {
      return expr;
    }

    return BoolConstant.True;
  }

  private boolean isProductExpr(SmtExpr expr)
  {
    // returns true if expr has the form (product A  (product B (product C (...))))
    // where A, B, C are variables
    if (expr instanceof Variable)
    {
      return true;
    }
    if (expr instanceof SmtBinaryExpr)
    {
      SmtBinaryExpr binaryExpr = (SmtBinaryExpr) expr;
      if (binaryExpr.getOp() != SmtBinaryExpr.Op.PRODUCT)
      {
        return false;
      }
      return isProductExpr(binaryExpr.getA()) && isProductExpr(binaryExpr.getB());
    }
    return false;
  }

  private SmtExpr optimizeOneArrowAnyMultiplicity(SmtExpr expr)
  {
    // change multiplicity translation for sig A {f: B one -> C}
    // original:
    // ---------
    //
    //(assert
    // (forall ((x Atom))
    //   (let ((xTuple (mkTuple x)))
    //     (=> (member xTuple A)
    //       (let ((s (join (singleton xTuple) f)))
    //         (and (subset s (product B C))
    //           (forall ((y Atom))
    //             (let ((yTuple (mkTuple y)))
    //               (=> (member yTuple C)
    //                 (exists ((z Atom))
    //                   (let ((zTuple (mkTuple z)))
    //                     (and (member zTuple B)
    //                       (member (mkTuple z y) s)
    //                       (forall ((w Atom))
    //                         (let ((wTuple (mkTuple w)))
    //                           (=>
    //                             (and (member wTuple B) (not (= wTuple zTuple)))
    //                             (not (member (mkTuple w y) s)))))))))))))))))

    // optimized:
    // ---------
    // (assert
    //  (forall ((x Atom))
    //    (=> (member (mkTuple x) A)
    //        (forall ((y Atom))
    //          (=>
    //            (member (mkTuple y) C)
    //            (exists (z Atom))
    //              (and
    //                (member (mkTuple z) B)
    //                (member (mkTuple x z y) f)
    //                (forall ((w Atom))
    //                  (=> (not (= w z))
    //                      (not (member (mkTuple x w y) f))
    //                  )
    //                ))))

    if (!(expr instanceof SmtQtExpr))
    {
      return expr;
    }

    SmtQtExpr smtQtExpr = (SmtQtExpr) expr;
    if (smtQtExpr.getOp() != SmtQtExpr.Op.FORALL || smtQtExpr.getVariables().size() != 1)
    {
      return expr;
    }
    SmtVariable x = smtQtExpr.getVariables().get(0);
    SmtExpr xTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable());
    if (!(smtQtExpr.getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let1 = (SmtLetExpr) smtQtExpr.getExpr();
    if (let1.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr t = let1.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr tExpr = let1.getLetVariables().values().stream().findFirst().get();
    if (!tExpr.equals(xTuple))
    {
      return expr;
    }
    if (!(let1.getSmtExpr() instanceof SmtBinaryExpr))
    {
      return expr;
    }
    SmtBinaryExpr implies = (SmtBinaryExpr) let1.getSmtExpr();
    if (implies.getOp() != SmtBinaryExpr.Op.IMPLIES)
    {
      return expr;
    }
    if (!(implies.getA() instanceof SmtBinaryExpr && implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtBinaryExpr operand1 = (SmtBinaryExpr) implies.getA();
    if (!(operand1.getOp() == SmtBinaryExpr.Op.MEMBER && operand1.getA().equals(t)))
    {
      return expr;
    }
    SmtExpr setA = operand1.getB();
    if (!(implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let2 = (SmtLetExpr) implies.getB();
    if (let2.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr s = let2.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr sExpr = let2.getLetVariables().values().stream().findFirst().get();
    if (!(sExpr instanceof SmtBinaryExpr))
    {
      return sExpr;
    }
    SmtExpr f = ((SmtBinaryExpr) sExpr).getB();
    SmtExpr singletonT = SmtUnaryExpr.Op.SINGLETON.make(t);
    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(singletonT, f);
    if (!sExpr.equals(join))
    {
      return expr;
    }

    if (!(let2.getSmtExpr() instanceof SmtMultiArityExpr &&
        ((SmtMultiArityExpr) let2.getSmtExpr()).getOp() == SmtMultiArityExpr.Op.AND))
    {
      return expr;
    }

    SmtMultiArityExpr and1 = (SmtMultiArityExpr) let2.getSmtExpr();
    if (and1.getExprs().size() != 2)
    {
      return expr;
    }
    SmtExpr subset = and1.get(0);
    SmtExpr forall1 = and1.get(1);
    if (!(subset instanceof SmtBinaryExpr) || ((SmtBinaryExpr) subset).getOp() != SmtBinaryExpr.Op.SUBSET)
    {
      return expr;
    }
    if (!((SmtBinaryExpr) subset).getA().equals(s))
    {
      return expr;
    }

    if (!(((SmtBinaryExpr) subset).getB() instanceof SmtBinaryExpr))
    {
      return expr;
    }

    SmtBinaryExpr product = (SmtBinaryExpr) ((SmtBinaryExpr) subset).getB();
    if (product.getOp() != SmtBinaryExpr.Op.PRODUCT)
    {
      return expr;
    }
    if (!(product.getA() instanceof Variable && product.getB() instanceof Variable))
    {
      return expr;
    }

    SmtExpr setB = product.getA();
    SmtExpr setC = product.getB();

    if (!(forall1 instanceof SmtQtExpr && ((SmtQtExpr) forall1).getOp() == SmtQtExpr.Op.FORALL))
    {
      return expr;
    }

    if (!(((SmtQtExpr) forall1).getVariables().size() == 1 &&
        ((SmtQtExpr) forall1).getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }

    SmtLetExpr let3 = (SmtLetExpr) ((SmtQtExpr) forall1).getExpr();
    if (let3.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtVariable y = ((SmtQtExpr) forall1).getVariables().get(0);
    Map.Entry<SmtVariable, SmtExpr> entry1 = let3.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry1.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable())))
    {
      return expr;
    }
    if (!(let3.getSmtExpr() instanceof SmtBinaryExpr &&
        ((SmtBinaryExpr) let3.getSmtExpr()).getOp() == SmtBinaryExpr.Op.IMPLIES))
    {
      return expr;
    }

    SmtBinaryExpr implies1 = (SmtBinaryExpr) let3.getSmtExpr();

    if (!implies1.getA().equals(SmtBinaryExpr.Op.MEMBER.make(entry1.getKey().getVariable(), setC)))
    {
      return expr;
    }

    if (!(implies1.getB() instanceof SmtQtExpr &&
        ((SmtQtExpr) implies1.getB()).getOp() == SmtQtExpr.Op.EXISTS &&
        ((SmtQtExpr) implies1.getB()).getVariables().size() == 1 &&
        ((SmtQtExpr) implies1.getB()).getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }


    SmtVariable z = ((SmtQtExpr) implies1.getB()).getVariables().get(0);

    SmtLetExpr let4 = (SmtLetExpr) ((SmtQtExpr) implies1.getB()).getExpr();
    Map.Entry<SmtVariable, SmtExpr> entry2 = let4.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry2.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(z.getVariable())))
    {
      return expr;
    }
    SmtExpr zTuple = entry2.getKey().getVariable();
    if (!(let4.getSmtExpr() instanceof SmtMultiArityExpr &&
        ((SmtMultiArityExpr) let4.getSmtExpr()).getOp() == SmtMultiArityExpr.Op.AND &&
        ((SmtMultiArityExpr) let4.getSmtExpr()).getExprs().size() == 3))
    {
      return expr;
    }
    SmtMultiArityExpr and2 = (SmtMultiArityExpr) let4.getSmtExpr();
    SmtExpr zyTuple = SmtMultiArityExpr.Op.MKTUPLE.make(z.getVariable(), y.getVariable());

    if (!(and2.get(0).equals(SmtBinaryExpr.Op.MEMBER.make(zTuple, setB)) &&
        and2.get(1).equals(SmtBinaryExpr.Op.MEMBER.make(zyTuple, s)) &&
        and2.get(2) instanceof SmtQtExpr &&
        ((SmtQtExpr) and2.get(2)).getOp() == SmtQtExpr.Op.FORALL &&
        ((SmtQtExpr) and2.get(2)).getVariables().size() == 1 &&
        ((SmtQtExpr) and2.get(2)).getExpr() instanceof SmtLetExpr &&
        ((SmtLetExpr) ((SmtQtExpr) and2.get(2)).getExpr()).getLetVariables().size() == 1
    ))
    {
      return expr;
    }

    SmtQtExpr forall2 = (SmtQtExpr) and2.get(2);
    SmtVariable w = forall2.getVariables().get(0);
    SmtLetExpr let5 = (SmtLetExpr) ((SmtQtExpr) and2.get(2)).getExpr();

    Map.Entry<SmtVariable, SmtExpr> entry3 = let5.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry3.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(w.getVariable())))
    {
      return expr;
    }

    SmtExpr wTuple = entry3.getKey().getVariable();
    SmtExpr and3 = SmtMultiArityExpr.Op.AND.make(
        SmtBinaryExpr.Op.MEMBER.make(wTuple, setB),
        SmtUnaryExpr.Op.NOT.make(SmtBinaryExpr.Op.EQ.make(wTuple, zTuple)));

    SmtExpr wyTuple = SmtMultiArityExpr.Op.MKTUPLE.make(w.getVariable(), y.getVariable());

    SmtExpr not = SmtUnaryExpr.Op.NOT.make(SmtBinaryExpr.Op.MEMBER.make(wyTuple, s));
    SmtExpr implies2 = SmtBinaryExpr.Op.IMPLIES.make(and3, not);
    if (!let5.getSmtExpr().equals(implies2))
    {
      return expr;
    }

    x = new SmtVariable("x", x.getSort(), false);
    y = new SmtVariable("y", y.getSort(), false);
    z = new SmtVariable("z", z.getSort(), false);
    w = new SmtVariable("w", w.getSort(), false);

    xTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable());
    SmtExpr yTuple = SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable());
    zTuple = SmtMultiArityExpr.Op.MKTUPLE.make(z.getVariable());
    wTuple = SmtMultiArityExpr.Op.MKTUPLE.make(w.getVariable());

    SmtExpr xzyTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), z.getVariable(), y.getVariable());
    SmtExpr xwyTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), w.getVariable(), y.getVariable());

    SmtExpr xMember = SmtBinaryExpr.Op.MEMBER.make(xTuple, setA);
    SmtExpr xzyMember = SmtBinaryExpr.Op.MEMBER.make(xzyTuple, f);
//    SmtExpr exists1 = SmtQtExpr.Op.EXISTS.make(xzyMember, y, z);
//    SmtExpr and4 = SmtMultiArityExpr.Op.AND.make(xMember, exists1);


    SmtExpr yMember = SmtBinaryExpr.Op.MEMBER.make(yTuple, setC);
    SmtExpr zMember = SmtBinaryExpr.Op.MEMBER.make(zTuple, setB);
    SmtExpr xwyMember = SmtBinaryExpr.Op.MEMBER.make(xwyTuple, f);
    SmtExpr xwyNotMember = SmtUnaryExpr.Op.NOT.make(xwyMember);

    SmtExpr wzEqual = SmtBinaryExpr.Op.EQ.make(w.getVariable(), z.getVariable());
    SmtExpr wzNotEqual = SmtUnaryExpr.Op.NOT.make(wzEqual);
    SmtExpr implies3 = SmtBinaryExpr.Op.IMPLIES.make(wzNotEqual, xwyNotMember);
    SmtExpr forall3 = SmtQtExpr.Op.FORALL.make(implies3, w);
    SmtExpr and5 = SmtMultiArityExpr.Op.AND.make(zMember, xzyMember, forall3);
    SmtExpr exists2 = SmtQtExpr.Op.EXISTS.make(and5, z);

    SmtExpr implies4 = SmtBinaryExpr.Op.IMPLIES.make(yMember, exists2);
    SmtExpr forall4 = SmtQtExpr.Op.FORALL.make(implies4, y);

    SmtExpr implies5 = SmtBinaryExpr.Op.IMPLIES.make(xMember, forall4);

    SmtExpr forall6 = SmtQtExpr.Op.FORALL.make(implies5, x);

    return forall6;
  }

  private SmtExpr optimizeAnyArrowOneMultiplicity(SmtExpr expr)
  {
    // change multiplicity translation for sig A {f: B one -> C}
    // original:
    // ---------
    //
    //(assert
    // (forall ((x Atom))
    //   (let ((xTuple (mkTuple x)))
    //     (=> (member xTuple A)
    //       (let ((s (join (singleton xTuple) f)))
    //         (and (subset s (product B C))
    //           (forall ((y Atom))
    //             (let ((yTuple (mkTuple y)))
    //               (=> (member yTuple B)
    //                 (exists ((z Atom))
    //                   (let ((zTuple (mkTuple z)))
    //                     (and (member zTuple C)
    //                       (member (mkTuple y z) s)
    //                       (forall ((w Atom))
    //                         (let ((wTuple (mkTuple w)))
    //                           (=>
    //                             (and (member wTuple C) (not (= wTuple zTuple)))
    //                             (not (member (mkTuple y w) s)))))))))))))))))

    // optimized:
    // ---------
    // (assert
    //  (forall ((x Atom))
    //    (=> (member (mkTuple x) A)
    //        (forall ((y Atom))
    //          (=>
    //            (member (mkTuple y) B)
    //            (exists (z Atom))
    //              (and
    //                (member (mkTuple z) C)
    //                (member (mkTuple x y z) f)
    //                (forall ((w Atom))
    //                  (=> (not (= w z))
    //                      (not (member (mkTuple x y w) f))
    //                  )
    //                ))))

    if (!(expr instanceof SmtQtExpr))
    {
      return expr;
    }

    SmtQtExpr smtQtExpr = (SmtQtExpr) expr;
    if (smtQtExpr.getOp() != SmtQtExpr.Op.FORALL || smtQtExpr.getVariables().size() != 1)
    {
      return expr;
    }
    SmtVariable x = smtQtExpr.getVariables().get(0);
    SmtExpr xTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable());
    if (!(smtQtExpr.getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let1 = (SmtLetExpr) smtQtExpr.getExpr();
    if (let1.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr t = let1.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr tExpr = let1.getLetVariables().values().stream().findFirst().get();
    if (!tExpr.equals(xTuple))
    {
      return expr;
    }
    if (!(let1.getSmtExpr() instanceof SmtBinaryExpr))
    {
      return expr;
    }
    SmtBinaryExpr implies = (SmtBinaryExpr) let1.getSmtExpr();
    if (implies.getOp() != SmtBinaryExpr.Op.IMPLIES)
    {
      return expr;
    }
    if (!(implies.getA() instanceof SmtBinaryExpr && implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtBinaryExpr operand1 = (SmtBinaryExpr) implies.getA();
    if (!(operand1.getOp() == SmtBinaryExpr.Op.MEMBER && operand1.getA().equals(t)))
    {
      return expr;
    }
    SmtExpr setA = operand1.getB();
    if (!(implies.getB() instanceof SmtLetExpr))
    {
      return expr;
    }
    SmtLetExpr let2 = (SmtLetExpr) implies.getB();
    if (let2.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtExpr s = let2.getLetVariables().keySet().stream().findFirst().get().getVariable();
    SmtExpr sExpr = let2.getLetVariables().values().stream().findFirst().get();
    if (!(sExpr instanceof SmtBinaryExpr))
    {
      return sExpr;
    }
    SmtExpr f = ((SmtBinaryExpr) sExpr).getB();
    SmtExpr singletonT = SmtUnaryExpr.Op.SINGLETON.make(t);
    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(singletonT, f);
    if (!sExpr.equals(join))
    {
      return expr;
    }

    if (!(let2.getSmtExpr() instanceof SmtMultiArityExpr &&
        ((SmtMultiArityExpr) let2.getSmtExpr()).getOp() == SmtMultiArityExpr.Op.AND))
    {
      return expr;
    }

    SmtMultiArityExpr and1 = (SmtMultiArityExpr) let2.getSmtExpr();
    if (and1.getExprs().size() != 2)
    {
      return expr;
    }
    SmtExpr subset = and1.get(0);
    SmtExpr forall1 = and1.get(1);
    if (!(subset instanceof SmtBinaryExpr) || ((SmtBinaryExpr) subset).getOp() != SmtBinaryExpr.Op.SUBSET)
    {
      return expr;
    }
    if (!((SmtBinaryExpr) subset).getA().equals(s))
    {
      return expr;
    }

    if (!(((SmtBinaryExpr) subset).getB() instanceof SmtBinaryExpr))
    {
      return expr;
    }

    SmtBinaryExpr product = (SmtBinaryExpr) ((SmtBinaryExpr) subset).getB();
    if (product.getOp() != SmtBinaryExpr.Op.PRODUCT)
    {
      return expr;
    }
    if (!(product.getA() instanceof Variable && product.getB() instanceof Variable))
    {
      return expr;
    }

    SmtExpr setB = product.getA();
    SmtExpr setC = product.getB();

    if (!(forall1 instanceof SmtQtExpr && ((SmtQtExpr) forall1).getOp() == SmtQtExpr.Op.FORALL))
    {
      return expr;
    }

    if (!(((SmtQtExpr) forall1).getVariables().size() == 1 &&
        ((SmtQtExpr) forall1).getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }

    SmtLetExpr let3 = (SmtLetExpr) ((SmtQtExpr) forall1).getExpr();
    if (let3.getLetVariables().size() != 1)
    {
      return expr;
    }
    SmtVariable y = ((SmtQtExpr) forall1).getVariables().get(0);
    Map.Entry<SmtVariable, SmtExpr> entry1 = let3.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry1.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable())))
    {
      return expr;
    }
    if (!(let3.getSmtExpr() instanceof SmtBinaryExpr &&
        ((SmtBinaryExpr) let3.getSmtExpr()).getOp() == SmtBinaryExpr.Op.IMPLIES))
    {
      return expr;
    }

    SmtBinaryExpr implies1 = (SmtBinaryExpr) let3.getSmtExpr();

    if (!implies1.getA().equals(SmtBinaryExpr.Op.MEMBER.make(entry1.getKey().getVariable(), setB)))
    {
      return expr;
    }

    if (!(implies1.getB() instanceof SmtQtExpr &&
        ((SmtQtExpr) implies1.getB()).getOp() == SmtQtExpr.Op.EXISTS &&
        ((SmtQtExpr) implies1.getB()).getVariables().size() == 1 &&
        ((SmtQtExpr) implies1.getB()).getExpr() instanceof SmtLetExpr))
    {
      return expr;
    }


    SmtVariable z = ((SmtQtExpr) implies1.getB()).getVariables().get(0);

    SmtLetExpr let4 = (SmtLetExpr) ((SmtQtExpr) implies1.getB()).getExpr();
    Map.Entry<SmtVariable, SmtExpr> entry2 = let4.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry2.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(z.getVariable())))
    {
      return expr;
    }
    SmtExpr zTuple = entry2.getKey().getVariable();
    if (!(let4.getSmtExpr() instanceof SmtMultiArityExpr &&
        ((SmtMultiArityExpr) let4.getSmtExpr()).getOp() == SmtMultiArityExpr.Op.AND &&
        ((SmtMultiArityExpr) let4.getSmtExpr()).getExprs().size() == 3))
    {
      return expr;
    }
    SmtMultiArityExpr and2 = (SmtMultiArityExpr) let4.getSmtExpr();
    SmtExpr yzTuple = SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable(), z.getVariable());

    if (!(and2.get(0).equals(SmtBinaryExpr.Op.MEMBER.make(zTuple, setC)) &&
        and2.get(1).equals(SmtBinaryExpr.Op.MEMBER.make(yzTuple, s)) &&
        and2.get(2) instanceof SmtQtExpr &&
        ((SmtQtExpr) and2.get(2)).getOp() == SmtQtExpr.Op.FORALL &&
        ((SmtQtExpr) and2.get(2)).getVariables().size() == 1 &&
        ((SmtQtExpr) and2.get(2)).getExpr() instanceof SmtLetExpr &&
        ((SmtLetExpr) ((SmtQtExpr) and2.get(2)).getExpr()).getLetVariables().size() == 1
    ))
    {
      return expr;
    }

    SmtQtExpr forall2 = (SmtQtExpr) and2.get(2);
    SmtVariable w = forall2.getVariables().get(0);
    SmtLetExpr let5 = (SmtLetExpr) ((SmtQtExpr) and2.get(2)).getExpr();

    Map.Entry<SmtVariable, SmtExpr> entry3 = let5.getLetVariables().entrySet().stream().findFirst().get();
    if (!entry3.getValue().equals(SmtMultiArityExpr.Op.MKTUPLE.make(w.getVariable())))
    {
      return expr;
    }

    SmtExpr wTuple = entry3.getKey().getVariable();
    SmtExpr and3 = SmtMultiArityExpr.Op.AND.make(
        SmtBinaryExpr.Op.MEMBER.make(wTuple, setC),
        SmtUnaryExpr.Op.NOT.make(SmtBinaryExpr.Op.EQ.make(wTuple, zTuple)));

    SmtExpr ywTuple = SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable(), w.getVariable());

    SmtExpr not = SmtUnaryExpr.Op.NOT.make(SmtBinaryExpr.Op.MEMBER.make(ywTuple, s));
    SmtExpr implies2 = SmtBinaryExpr.Op.IMPLIES.make(and3, not);
    if (!let5.getSmtExpr().equals(implies2))
    {
      return expr;
    }

    x = new SmtVariable("x", x.getSort(), false);
    y = new SmtVariable("y", y.getSort(), false);
    z = new SmtVariable("z", z.getSort(), false);
    w = new SmtVariable("w", w.getSort(), false);

    xTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable());
    SmtExpr yTuple = SmtMultiArityExpr.Op.MKTUPLE.make(y.getVariable());
    zTuple = SmtMultiArityExpr.Op.MKTUPLE.make(z.getVariable());
    wTuple = SmtMultiArityExpr.Op.MKTUPLE.make(w.getVariable());

    SmtExpr xyzTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), y.getVariable(), z.getVariable());
    SmtExpr xywTuple = SmtMultiArityExpr.Op.MKTUPLE.make(x.getVariable(), y.getVariable(), w.getVariable());

    SmtExpr xMember = SmtBinaryExpr.Op.MEMBER.make(xTuple, setA);
    SmtExpr xyzMember = SmtBinaryExpr.Op.MEMBER.make(xyzTuple, f);

    SmtExpr yMember = SmtBinaryExpr.Op.MEMBER.make(yTuple, setB);
    SmtExpr zMember = SmtBinaryExpr.Op.MEMBER.make(zTuple, setC);
    SmtExpr xywMember = SmtBinaryExpr.Op.MEMBER.make(xywTuple, f);
    SmtExpr xywNotMember = SmtUnaryExpr.Op.NOT.make(xywMember);

    SmtExpr wzEqual = SmtBinaryExpr.Op.EQ.make(w.getVariable(), z.getVariable());
    SmtExpr wzNotEqual = SmtUnaryExpr.Op.NOT.make(wzEqual);
    SmtExpr implies3 = SmtBinaryExpr.Op.IMPLIES.make(wzNotEqual, xywNotMember);
    SmtExpr forall3 = SmtQtExpr.Op.FORALL.make(implies3, w);
    SmtExpr and5 = SmtMultiArityExpr.Op.AND.make(zMember, xyzMember, forall3);
    SmtExpr exists2 = SmtQtExpr.Op.EXISTS.make(and5, z);

    SmtExpr implies4 = SmtBinaryExpr.Op.IMPLIES.make(yMember, exists2);
    SmtExpr forall4 = SmtQtExpr.Op.FORALL.make(implies4, y);

    SmtExpr implies5 = SmtBinaryExpr.Op.IMPLIES.make(xMember, forall4);

    SmtExpr forall6 = SmtQtExpr.Op.FORALL.make(implies5, x);

    return forall6;
  }

  @Override
  public SmtRewriteResult visit(SmtMultiArityExpr original)
  {
    List<SmtRewriteResult> results = new ArrayList<>();
    for (SmtExpr expr : original.getExprs())
    {
      SmtRewriteResult exprResult = visit(expr);
      results.add(exprResult);
    }
    List<SmtExpr> exprs = results.stream()
                                 .map(r -> (SmtExpr) r.smtAst)
                                 .collect(Collectors.toList());

    SmtMultiArityExpr multiArityExpr = original.getOp().make(exprs);
    SmtRewriteResult result = removeTrivialTerms(multiArityExpr);
    if (result.smtAst instanceof SmtMultiArityExpr)
    {
      result = flattenNestedExprs((SmtMultiArityExpr) result.smtAst, result.status);
    }
    return result;
  }

  @Override
  public SmtRewriteResult visit(SmtCallExpr smtCallExpr)
  {
    List<SmtRewriteResult> results = new ArrayList<>();

    for (SmtExpr expr : smtCallExpr.getArguments())
    {
      SmtRewriteResult exprResult = visit(expr);
      results.add(exprResult);
    }

    List<SmtExpr> exprs = results.stream()
                                 .map(r -> (SmtExpr) r.smtAst)
                                 .collect(Collectors.toList());
    SmtExpr smtAst = new SmtCallExpr(smtCallExpr.getFunction(), exprs);
    return SmtRewriteResult.Status.Done.make(smtAst);
  }

  @Override
  public SmtRewriteResult visit(SmtVariable smtVariable)
  {
    return SmtRewriteResult.Status.Done.make(smtVariable);
  }

  @Override
  public SmtRewriteResult visit(BoolSort boolSort)
  {
    return SmtRewriteResult.Status.Done.make(boolSort);
  }

  @Override
  public SmtRewriteResult visit(SmtLetExpr smtLetExpr)
  {
    return optimizedTupleSelectZeroForUnaryTuples(smtLetExpr);
  }

  @Override
  public SmtRewriteResult visit(SmtIteExpr ite)
  {
    SmtRewriteResult conditionResult = visit(ite.getCondExpr());
    SmtRewriteResult thenResult = visit(ite.getThenExpr());
    SmtRewriteResult elseResult = visit(ite.getElseExpr());
    SmtExpr smtAst = new SmtIteExpr((SmtExpr) conditionResult.smtAst,
        (SmtExpr) thenResult.smtAst,
        (SmtExpr) elseResult.smtAst);
    return SmtRewriteResult.Status.Done.make(smtAst);
  }

  @Override
  public SmtRewriteResult visit(UninterpretedConstant uninterpretedConstant)
  {
    return SmtRewriteResult.Status.Done.make(uninterpretedConstant);
  }

  @Override
  public SmtRewriteResult visit(SmtSettings smtSettings)
  {
    return SmtRewriteResult.Status.Done.make(smtSettings);
  }

  @Override
  public SmtRewriteResult visit(SmtValues smtValues)
  {
    return SmtRewriteResult.Status.Done.make(smtValues);
  }

  @Override
  public SmtRewriteResult visit(ExpressionValue expressionValue)
  {
    return SmtRewriteResult.Status.Done.make(expressionValue);
  }

  @Override
  public SmtRewriteResult visit(SmtUnsatCore smtUnsatCore)
  {
    return SmtRewriteResult.Status.Done.make(smtUnsatCore);
  }
}
