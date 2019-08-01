package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class MultiplicityTests
{
    @Test
    public void oneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void oneOneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A one -> one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void oneLoneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A one -> lone A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneLoneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A lone -> lone A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneOneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A lone -> one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void oneSomeDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A one -> some A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someOneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A some -> one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someSomeDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A some -> some A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneSomeDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A lone -> some A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someLoneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A some -> lone A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void oneSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A one -> set A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void setOneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A set -> one A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A lone -> set A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void setLoneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A set -> lone A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void setSomeDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A set -> some A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A some -> set A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void setSetDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: A set -> set A | some A}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void loneDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {#A = 1 and some x: lone A | lone x and no x}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void someDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: some A | lone x and no x}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    public void setDeclaration() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: set A | no x}";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void noneDeclaration1() throws Exception
    {
        String alloy =  "sig A {} fact f {some x: A | no x}";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    public void noneDeclaration2() throws Exception
    {
        String alloy =  "sig A {} pred p[a: A]{ no a} run p";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    public void multipleQuantifiers() throws Exception
    {
        String alloy =  "sig A {}\n" +
                " fact f1 {some a, b : A  ->  A | some a & b}\n" +
                " fact f2 {all a, b : one A | some a & b }";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }

    @Test
    public void multipleQuantifiersWithInt() throws Exception
    {
        String alloy =   "sig A {}\n" +
                " fact f1 {some a, b : A  ->  Int | some a & b}\n" +
                " fact f2 {all a, b : one A | some a & b }";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
    }
}
