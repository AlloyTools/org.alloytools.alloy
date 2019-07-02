package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class CourseExamplesTests
{

    @Test
    public void academia_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia.als", true, 0);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void academia_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void academia_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia.als", true, 2);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void academia1_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-1.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void academia1_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-1.als", true, 1);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void academia1_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-1.als", true, 2);
        assertEquals("unsat", result.satResult);
    }


    @Test
    public void academia1_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-1.als", true, 3);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void academia1a() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-1a.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void academia2_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-2.als", true, 0);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void academia2_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-2.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void academia2_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-2.als", true, 2);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void academia3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-3.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void academia3a() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/academia-3a.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void adam_eve_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/adam_eve.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void adam_eve_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/adam_eve.als", true, 1);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void adam_eve_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/adam_eve.als", true, 2);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void adam_eve_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/adam_eve.als", true, 3);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void family1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-1.als", true, 0);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void family2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-2.als", true, 0);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void family3_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 0);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void family3_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 1);
        assertEquals("unsat", result.satResult);
    }


    @Test
    public void family3_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 2);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void family3_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 3);
        assertEquals("sat", result.satResult);
    }


    @Test
    public void family3_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 4);
        assertEquals("unsat", result.satResult);
    }


    @Test
    public void family3_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-3.als", true, 5);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 0);

        assertEquals("unsat", result.satResult);        
    }

    @Test
    public void family4_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 2);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 3);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 4);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family4_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 5);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 6);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family4_7() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 7);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family4_8() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-4.als", true, 8);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family5_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family5_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family5_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family5_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 3);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family5_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 4);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family5_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 5);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family5_6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 6);

        assertEquals("sat", result.satResult);
    }
    @Test
    public void family5_7() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 7);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family5_8() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-5.als", true, 8);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-6.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family7_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 0);

        assertEquals("sat", result.satResult);
    }


    @Test
    public void family7_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family7_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family7_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 3);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family7_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 4);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family7_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 5);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family7_6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 6);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void family7_7() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 7);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void family7_8() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/family-7.als", true, 8);

        assertEquals("unsat", result.satResult);
    }



    @Test
    public void hotel1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/hotel1.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void hotel2_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/hotel2.als", true, 0);
        assertEquals("unsat", result.satResult);
    }


    @Test
    public void hotel2_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/hotel2.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void rover() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("./test/rover.als", true, 0);
        assertEquals("sat", result.satResult);
    }
}
