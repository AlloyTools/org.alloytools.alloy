package edu.uiowa.smt.optimizer;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.smtAst.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SmtOptimizerTests
{
  private SmtScript script = new SmtScript();
  private SmtRewriter rewriter = new SmtRewriter();

  @BeforeEach
  private void reset()
  {
    script.reset();
  }

  @Test
  public void trivialAssertions()
  {
    script.addAssertion(new Assertion("", "", BoolConstant.True));
    SmtExpr andTrue = SmtMultiArityExpr.Op.AND.make(BoolConstant.True);
    script.addAssertion(new Assertion("", "", andTrue));
    SmtExpr orTrue = SmtMultiArityExpr.Op.OR.make(BoolConstant.True);
    script.addAssertion(new Assertion("", "", orTrue));

    script = (SmtScript) rewriter.visit(script).smtAst;

    // all trivial assertions should be filtered out.
    assertTrue(script.getAssertions().isEmpty());
  }

  @Test
  public void unusedUninterpretedInt()
  {
    script.addFunctions(AbstractTranslator.getUninterpretedIntFunctions(script));

    script = (SmtScript) rewriter.visit(script).smtAst;

    // all trivial assertions should be filtered out.
    assertTrue(script.getFunctions().isEmpty());
  }

  @Test
  public void empty() throws Exception
  {
    String alloy = "";

    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("sat", commandResults.get(0).satResult);
  }

  @Test
  public void command() throws Exception
  {
    String alloy = "run {some x: Int | x = 2}";

    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("sat", commandResults.get(0).satResult);
  }

  @Test
  public void tupleSelect() throws Exception
  {
    // (assert (let ((x (mkTuple a))) (= ((_ tupSel 0) x) 5))) is optimized to
    // (assert (let ((x (mkTuple a))) (= (a 5)))

    SmtExpr zero = new IntConstant("0");
    SmtExpr five = new IntConstant("5");
    SmtVariable a = new SmtVariable("a", IntSort.getInstance(), false);
    SmtVariable x = new SmtVariable("x", new TupleSort(IntSort.getInstance()), false);
    SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(a.getVariable());
    SmtExpr tupleSelect = SmtBinaryExpr.Op.TUPSEL.make(zero, x.getVariable());
    SmtExpr equal = SmtBinaryExpr.Op.EQ.make(tupleSelect, five);
    Map<SmtVariable, SmtExpr> variables = new HashMap<>();
    variables.put(x, tuple);
    SmtExpr letExpr = new SmtLetExpr(variables, equal);

    SmtExpr optimizedEqual = SmtBinaryExpr.Op.EQ.make(a.getVariable(), five);
    SmtExpr expected = new SmtLetExpr(variables, optimizedEqual);

    SmtExpr actual = (SmtExpr) rewriter.visit(letExpr).smtAst;
    assertEquals(expected, actual);
  }

  @Test
  public void removeTrueConjuctsInAndExpr() throws Exception
  {
    // (assert (let ((x (mkTuple a))) (= ((_ tupSel 0) x) 5))) is optimized to
    // (assert (let ((x (mkTuple a))) (= (a 5)))

    SmtExpr zero = new IntConstant("0");
    SmtExpr five = new IntConstant("5");
    SmtVariable a = new SmtVariable("a", IntSort.getInstance(), false);
    SmtVariable x = new SmtVariable("x", new TupleSort(IntSort.getInstance()), false);
    SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(a.getVariable());
    SmtExpr tupleSelect = SmtBinaryExpr.Op.TUPSEL.make(zero, x.getVariable());
    SmtExpr equal = SmtBinaryExpr.Op.EQ.make(tupleSelect, five);
    Map<SmtVariable, SmtExpr> variables = new HashMap<>();
    variables.put(x, tuple);
    SmtExpr letExpr = new SmtLetExpr(variables, equal);

    SmtExpr optimizedEqual = SmtBinaryExpr.Op.EQ.make(a.getVariable(), five);
    SmtExpr expected = new SmtLetExpr(variables, optimizedEqual);

    SmtExpr actual = (SmtExpr) rewriter.visit(letExpr).smtAst;
    assertEquals(expected, actual);
  }

  @Test
  public void subsetMultiplicity() throws Exception
  {
    String alloy = "sig B, C, D, E {}\n" +
        "sig A { f  : B -> C, g : B -> C -> D }";

    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("sat", commandResults.get(0).satResult);
  }
}