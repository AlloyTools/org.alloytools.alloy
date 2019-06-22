package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

class ExprLetTranslatorTests
{
    @Test
    void comprehension() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "one sig A0 extends A{}\n" +
                "fun different[a: A]: A { let x = { b: A | a != b} |  x}\n" +
                "run {different[A0] != none}";
        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);
        assertEquals("sat", commandResults.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(2, aAtoms.size());

        FunctionDefinition a0 = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A0");
        Set<String> a0Atoms = TranslatorUtils.getAtomSet(a0);
        assertEquals(1, a0Atoms.size());
    }
}
