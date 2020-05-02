package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Bugs
{
  @Test
  public void test1() throws Exception
  {
    String alloy = "sig a in Int {} one sig a0 in a {}";
    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("sat", commandResults.get(0).satResult);

    FunctionDefinition A = TranslatorUtils.getFunctionDefinition(commandResults.get(0).smtModel, "this/a");
    Set<Integer> atoms = TranslatorUtils.getIntSet(A);
    assertEquals(1, atoms.size());
  }

  @Test
  public void test2() throws Exception
  {
    String alloy = "sig A {f: lone A} check {no a: A | #(a.f) > 1}";
    List<CommandResult> results = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("unsat", results.get(0).satResult);
  }

  @Test
  public void test3() throws Exception
  {
    String alloy = "sig A { id: Int }\n" +
        "pred P1 [p : set A]\n" +
        "{\n" +
        "  one a: p | a.id = 1\n" +
        "}\n" +
        "pred P2[p : set A] {\n" +
        "  P1[ { x : p | x.id > 0 } ]\n" +
        "}\n" +
        "run {\n" +
        "  some a : set A | P2[a]\n" +
        "}";

    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
    assertEquals("sat", commandResults.get(0).satResult);
  }

  @Test
  public void Test4() throws Exception
  {
    String alloy = "sig A { id: Int }\n" +
        "pred P1 [p : set A]\n" +
        "{\n" +
        "one a: p | a.id = 1\n" +
        "}\n" +
        "pred P2[p : set A] {\n" +
        "P1[ { x : p | x.id > 0 } ]\n" +
        "}\n" +
        "run {\n" +
        "some a : set A | P2[a]\n" +
        "} for 1 Int";

    List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, true);
    assertEquals("unsat", commandResults.get(0).satResult);
  }
}
