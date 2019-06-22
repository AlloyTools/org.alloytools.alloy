package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class CommandTests
{

    @Test
    void defaultCommand()
    {
        String alloy = "sig A {}\n";
        Translation translation = Utils.translate(alloy);
        assertEquals(1, translation.getCommands().size());
    }

    @Test
    void runCommand() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "run command1 {#A = 1 or #A = 2} for 10\n" +
                "run command1 {no A} for 10";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
        FunctionDefinition a = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/A");
        Set<String> atoms = TranslatorUtils.getAtomSet(a);
        assertTrue(1 ==  atoms.size() || 2 == atoms.size());

        assertEquals ("sat", results.get(1).satResult);
        a = TranslatorUtils.getFunctionDefinition( results.get(1).smtModel, "this/A");
        atoms = TranslatorUtils.getAtomSet(a);
        assertTrue(0 ==  atoms.size());
    }

    @Test
    void checkCommand() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "assert command1{some A}\n" +
                "check command1 for 10\n" +
                "assert command2 {some A or no A} \n" +
                "check command2 for 10\n";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
        assertEquals ("unsat", results.get(1).satResult);
    }

    @Test
    void predicate1 () throws Exception
    {
        String alloy = "sig a{} pred p[]{#a > 2} run p for 4";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
        FunctionDefinition a = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a");
        Set<String> atoms = TranslatorUtils.getAtomSet(a);
        assertEquals (3, atoms.size());
    }

    @Test
    void scope1() throws Exception
    {
        String alloy = "sig A {} run {} for exactly 3 A";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);
        assertEquals ("sat", results.get(0).satResult);
        FunctionDefinition A = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/A");
        Set<String> atoms = TranslatorUtils.getAtomSet(A);
        assertEquals (3, atoms.size());
    }

    @Test
    void scope2() throws Exception
    {
        String alloy = "sig a, b {}\n" +
                "run {} for  exactly 1 a, exactly 2 b\n" +
                "run {} for  exactly 3 a, exactly 4 b";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);

        assertEquals ("sat", results.get(0).satResult);

        FunctionDefinition a = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a");
        Set<String> atomsA = TranslatorUtils.getAtomSet(a);
        assertEquals (1, atomsA.size());

        FunctionDefinition b = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/b");
        Set<String> atomsB = TranslatorUtils.getAtomSet(b);
        assertEquals (2, atomsB.size());

        a = TranslatorUtils.getFunctionDefinition( results.get(1).smtModel, "this/a");
        atomsA = TranslatorUtils.getAtomSet(a);
        assertEquals (3, atomsA.size());

        b = TranslatorUtils.getFunctionDefinition( results.get(1).smtModel, "this/b");
        atomsB = TranslatorUtils.getAtomSet(b);
        assertEquals (4, atomsB.size());
    }

    @Test
    void scope3() throws Exception
    {
        String alloy = "sig a, b {}\n" +
                "run {} for 3 but exactly 2 a";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);

        assertEquals ("sat", results.get(0).satResult);

        FunctionDefinition a = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a");
        Set<String> atomsA = TranslatorUtils.getAtomSet(a);
        assertEquals (2, atomsA.size());

        FunctionDefinition b = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/b");
        Set<String> atomsB = TranslatorUtils.getAtomSet(b);
        assertEquals (0, atomsB.size());
    }

    @Test
    void scope4Abstract() throws Exception
    {
        String alloy = "abstract sig a, b {}\n" +
                "sig a0, a1 extends a {}\n" +
                "run {} for 3 but exactly 2 a0, exactly 1 a1";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);

        assertEquals ("sat", results.get(0).satResult);

        FunctionDefinition a0 = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a0");
        Set<String> atomsA0 = TranslatorUtils.getAtomSet(a0);
        assertEquals (2, atomsA0.size());

        FunctionDefinition a1 = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a1");
        Set<String> atomsA1 = TranslatorUtils.getAtomSet(a1);
        assertEquals (1, atomsA1.size());
    }

    @Test
    void scope5Abstract() throws Exception
    {
        String alloy = "abstract sig a {}\n" +
                "sig a0, a1, a2 extends a {}\n" +
                "run {} for 2 but exactly 2 a0, exactly 2 a1, exactly 1 a2";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);

        assertEquals ("sat", results.get(0).satResult);

        FunctionDefinition a = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a");
        Set<String> atomsA = TranslatorUtils.getAtomSet(a);
        assertEquals (5, atomsA.size());

        FunctionDefinition a0 = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a0");
        Set<String> atomsA0 = TranslatorUtils.getAtomSet(a0);
        assertEquals (2, atomsA0.size());

        FunctionDefinition a1 = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a1");
        Set<String> atomsA1 = TranslatorUtils.getAtomSet(a1);
        assertEquals (2, atomsA1.size());

        FunctionDefinition a2 = TranslatorUtils.getFunctionDefinition( results.get(0).smtModel, "this/a2");
        Set<String> atomsA2 = TranslatorUtils.getAtomSet(a2);
        assertEquals (1, atomsA2.size());
    }

    @Test
    void scope6() throws Exception
    {
        String alloy = "sig a {} fact {#a = 5}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);
        // default scope is 4, so the formula #a = 5 is unsat
        assertEquals ("unsat", results.get(0).satResult);
    }

    @Test
    void scope7() throws Exception
    {
        String alloy = "abstract sig A {}\n" +
                "sig A0, A1 extends A{}\n" +
                "run {#A = 3} for 1 but  exactly 2 A0\n" +
                "run {#A = 2} for 1 but  exactly 2 A0\n" +
                "run {#A = 3} for 1 but  exactly 2 A0, exactly 2 A1\n" +
                "run {#A = 4} for 1 but  exactly 2 A0, exactly 2 A1\n" +
                "run {#A = 3} for 1 but  2 A0\n" +
                "run {#A = 2} for 1 but  2 A0\n" +
                "run {#A = 3} for 1 but  2 A0, 2 A1\n" +
                "run {#A = 4} for 1 but  2 A0, 2 A1\n" +
                "run {#A = 3} \n" +
                "run {#A = 4}";
        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, true);

        assertEquals ("unsat", results.get(0).satResult);
        assertEquals ("sat", results.get(1).satResult);
        assertEquals ("unsat", results.get(2).satResult);
        assertEquals ("sat", results.get(3).satResult);
        assertEquals ("unsat", results.get(4).satResult);
        assertEquals ("sat", results.get(5).satResult);
        assertEquals ("sat", results.get(6).satResult);
        assertEquals ("sat", results.get(7).satResult);
        assertEquals ("sat", results.get(8).satResult);
        assertEquals ("unsat", results.get(9).satResult);
    }
}