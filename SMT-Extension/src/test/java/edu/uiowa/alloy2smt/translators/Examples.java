package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Examples
{
  @Test
  public void alloy_syntax1() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/alloy_syntax1.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void alloy_syntax2() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/alloy_syntax2.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void barber() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/barber.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void comprehension_0() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/comprehension.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void comprehension_1() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/comprehension.als", true, 1);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void filesystem_0() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/filesystem.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void filesystem_1() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/filesystem.als", true, 1);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void filesystem_2() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/filesystem.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void int1() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/int1.als", true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void int2() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/int2.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void int3() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/int3.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void int4() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/int4.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void ordering() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/ordering.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void test_0() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/test.als", true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void test_1() throws Exception
  {
    CommandResult result = AlloyUtils.runAlloyFile("./examples/test.als", true, 1);
    assertEquals("unsat", result.satResult);
  }
}
