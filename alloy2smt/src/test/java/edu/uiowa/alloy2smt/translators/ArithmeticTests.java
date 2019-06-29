package edu.uiowa.alloy2smt.translators;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import org.junit.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ArithmeticTests
{
    @Test
    public void union() throws Exception
    {
        String alloy = "sig a in Int {} fact {a = 6 + 8}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        Set<Integer> set = TranslatorUtils.getIntSet(a);
        assertEquals(set, new HashSet<>(Arrays.asList(6, 8)));
    }

    @Test
    public void singletons() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {}\n" +
                "fact {\n" +
                "#a = 1\n" +
                "#b = 1\n" +
                "1 = 1\n" +
                "plus[a, b] = 2\n" +
                "plus[c, 0] = 2\n" +
                "}\n";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        FunctionDefinition b = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/b");
        FunctionDefinition c = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/c");

        int aValue = TranslatorUtils.getInt(a);
        int bValue = TranslatorUtils.getInt(b);
        int cValue = TranslatorUtils.getInt(c);
        assertEquals(2, aValue + bValue);
        assertEquals(2, cValue);
    }

    @Test
    public void sets() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "a = 1+2 \n" +
                "b = 4+6 \n" +
                "plus[a, b] = c\n" +
                "}";
                  List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        Set<Integer> aSet = TranslatorUtils.getIntSet(a);
        assertEquals(aSet, new HashSet<>(Arrays.asList(1, 2)));
        FunctionDefinition b = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/b");
        Set<Integer> bSet = TranslatorUtils.getIntSet(b);
        assertEquals(bSet, new HashSet<>(Arrays.asList(4, 6)));
        FunctionDefinition c = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/c");
        Set<Integer> cSet = TranslatorUtils.getIntSet(c);
        assertEquals(cSet, new HashSet<>(Arrays.asList(5, 7, 6, 8)));
    }

    @Test
    public void plusMinus() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "plus[a, b] = c \n" +
                "minus[a,b] = c\n" +
                "}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition b = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/b");
        Set<Integer> bSet = TranslatorUtils.getIntSet(b);
        assertEquals(bSet, new HashSet<>(Arrays.asList(0)));
    }

    @Test
    public void remainder() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "#a = 2\n" +
                "8 in a\n" +
                "6 in a\n" +
                "#b = 1\n" +
                "rem[a,b] = c\n" +
                "}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition mod = AlloyUtils.getFunctionDefinition(commandResults.get(0), AbstractTranslator.mod);
    }

    @Test
    public void unsatPlusMinus() throws Exception
    {
        String alloy =
                "sig a, b, c, d in Int {}\n" +
                "fact add{plus[a,b] = c + d}\n" +
                "fact subtract{minus[a,b] = c - d}\n" +
                "fact notEqual{a != c and b != d}\n" +
                "fact nonzero {a > 0 and b > 0 and c > 0 and d > 0}\n";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    public void sum() throws Exception
    {
        String alloy = "sig a, b, c in Int {}\n" +
                "fact {sum [a] = 1  and sum[b] = 2 and sum[c] = 3}";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        Set<Integer> aSet = TranslatorUtils.getIntSet(a);
        assertEquals(aSet, new HashSet<>(Arrays.asList(1)));

        FunctionDefinition b = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/b");
        Set<Integer> bSet = TranslatorUtils.getIntSet(b);
        assertEquals(bSet, new HashSet<>(Arrays.asList(2)));

        FunctionDefinition c = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/c");
        Set<Integer> cSet = TranslatorUtils.getIntSet(c);
        assertEquals(cSet, new HashSet<>(Arrays.asList(3)));
    }

    @Test
    public void sumUnsat() throws Exception
    {
        String alloy = "sig a, b, c in Int {}\n" +
                "fact {sum [a] = 1  and sum[b] = 2 and sum[c] = 3 and #c = 3}";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("unsat", commandResults.get(0).satResult);
    }

    @Test
    public void GT() throws Exception
    {
        String alloy = "sig a in Int {} fact {a > 2}";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/a");
        int aValue = TranslatorUtils.getInt(a);
        assertTrue(aValue > 2);
    }

    @Test
    public void quantifiers() throws Exception
    {
        String alloy = "sig A in Int {}\n" +
                "fact {#A = 3 and all x, y: A | plus[x, y] < 10}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
    }

    @Test
    public void bug () throws Exception
    {
        String alloy = "sig A in Int {}\n" +
                "fact {A > 20 and #A  = 2}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertTrue(commandResults.size() == 1);
        assertEquals("sat", commandResults.get(0).satResult);
    }
}
