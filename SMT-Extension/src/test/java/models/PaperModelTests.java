package models;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class PaperModelTests
{

  @Test
  public void ab_ai() throws Exception
  {
    String fileName = "./test/paper/ab-ai.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void ab_dua() throws Exception
  {
    String fileName = "./test/paper/ab-dua.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void abt_dua() throws Exception
  {
    String fileName = "./test/paper/abt-dua.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void abt_ly_p() throws Exception
  {
    String fileName = "./test/paper/abt-ly-p.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void abt_ly_u() throws Exception
  {
    String fileName = "./test/paper/abt-ly-u.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void academia_0() throws Exception
  {
    String fileName = "./test/paper/academia_0.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void academia_1() throws Exception
  {
    String fileName = "./test/paper/academia_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void academia_2() throws Exception
  {
    String fileName = "./test/paper/academia_2.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void academia_3() throws Exception
  {
    String fileName = "./test/paper/academia_3.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void academia_4() throws Exception
  {
    String fileName = "./test/paper/academia_4.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void birthday() throws Exception
  {
    String fileName = "./test/paper/birthday.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void cf_0() throws Exception
  {
    String fileName = "./test/paper/cf_0.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void cf_1() throws Exception
  {
    String fileName = "./test/paper/cf_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void com_1() throws Exception
  {
    String fileName = "./test/paper/com-1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void com_2() throws Exception
  {
    String fileName = "./test/paper/com-2.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void com_3() throws Exception
  {
    String fileName = "./test/paper/com-3.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void com_4a() throws Exception
  {
    String fileName = "./test/paper/com-4a.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void com_4b() throws Exception
  {
    String fileName = "./test/paper/com-4b.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void family_1() throws Exception
  {
    String fileName = "./test/paper/family_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void family_2() throws Exception
  {
    String fileName = "./test/paper/family_2.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void farmers_1() throws Exception
  {
    String fileName = "./test/paper/farmers_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void fs_nda() throws Exception
  {
    String fileName = "./test/paper/fs-nda.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void fs_sd() throws Exception
  {
    String fileName = "./test/paper/fs-sd.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void gc_c() throws Exception
  {
    String fileName = "./test/paper/gc-c.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void gc_s1() throws Exception
  {
    String fileName = "./test/paper/gc-s1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void gc_s2() throws Exception
  {
    String fileName = "./test/paper/gc-s2.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void genealogy() throws Exception
  {
    String fileName = "./test/paper/genealogy.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void gp_nsf() throws Exception
  {
    String fileName = "./test/paper/gp-nsf.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void gp_nsg() throws Exception
  {
    String fileName = "./test/paper/gp-nsg.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void hr_l() throws Exception
  {
    String fileName = "./test/paper/hr-l.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void INSLabel() throws Exception
  {
    String fileName = "./test/paper/INSLabel.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void javatypes() throws Exception
  {
    String fileName = "./test/paper/javatypes.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void library() throws Exception
  {
    String fileName = "./test/paper/library.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void lights() throws Exception
  {
    String fileName = "./test/paper/lights.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void loc_int() throws Exception
  {
    String fileName = "./test/paper/loc_int.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void mem_wi() throws Exception
  {
    String fileName = "./test/paper/mem-wi.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("unsat", result.satResult);
  }

  @Test
  public void mem_wr() throws Exception
  {
    String fileName = "./test/paper/mem-wr.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void numbering_1() throws Exception
  {
    String fileName = "./test/paper/numbering_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void railway() throws Exception
  {
    String fileName = "./test/paper/railway.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void set() throws Exception
  {
    String fileName = "./test/paper/set.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("sat", result.satResult);
  }

  @Test
  public void social_1() throws Exception
  {
    String fileName = "./test/paper/social_1.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void social_2() throws Exception
  {
    String fileName = "./test/paper/social_2.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void social_3() throws Exception
  {
    String fileName = "./test/paper/social_3.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void social_4() throws Exception
  {
    String fileName = "./test/paper/social_4.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void social_5() throws Exception
  {
    String fileName = "./test/paper/social_5.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void social_6() throws Exception
  {
    String fileName = "./test/paper/social_6.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }

  @Test
  public void views() throws Exception
  {
    String fileName = "./test/paper/views.als";
    CommandResult result = AlloyUtils.runAlloyFile(fileName, true, 0);
    assertEquals("", result.satResult);
  }
}
