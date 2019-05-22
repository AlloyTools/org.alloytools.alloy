package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class CourseExamplesTests
{

    @Test
    public void academia() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
    }

    @Test
    public void academia1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia-1.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void academia1a() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia-1a.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void academia2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia-2.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
    }

    @Test
    public void academia3() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia-3.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void academia3a() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/academia-3a.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void adam_eve() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/adam_eve.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void family1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-1.als", true);
        assertEquals("sat", results.get(0).satResult);
    }


    @Test
    public void family2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-2.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void family3() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-3.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("sat", results.get(5).satResult);
    }

    @Test
    public void family4() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-4.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("sat", results.get(5).satResult);
        assertEquals("sat", results.get(6).satResult);
        assertEquals("unsat", results.get(7).satResult);
        assertEquals("sat", results.get(8).satResult);
    }

    @Test
    public void family5() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-5.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("sat", results.get(5).satResult);
        assertEquals("sat", results.get(6).satResult);
        assertEquals("unsat", results.get(7).satResult);
        assertEquals("sat", results.get(8).satResult);
    }

    @Test
    public void family6() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-6.als", true);

        assertEquals("sat", results.get(0).satResult);
    }


    @Test
    public void family7() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/family-7.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("sat", results.get(4).satResult);
        assertEquals("sat", results.get(5).satResult);
        assertEquals("sat", results.get(6).satResult);
        assertEquals("unsat", results.get(7).satResult);
        assertEquals("unsat", results.get(8).satResult);
    }

    @Test
    public void hotel1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/hotel1.als", true);

        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void hotel2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/hotel2.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void rover() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("./test/rover.als", true);
        assertEquals("sat", results.get(0).satResult);
    }
}
