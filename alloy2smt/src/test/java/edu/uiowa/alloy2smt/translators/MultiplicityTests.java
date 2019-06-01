package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class MultiplicityTests
{
    @Test
    public void oneSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void oneOneSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A one -> one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: lone A | lone x and no x}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: some A | lone x and no x}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    public void setSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: set A | no x}";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void noneSetDeclaration1() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: A | no x}";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    public void noneSetDeclaration2() throws Exception
    {
        String alloy =  "sig A {} pred p[a: A]{ no a} run p";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }
}
