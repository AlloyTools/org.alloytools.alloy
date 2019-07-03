package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ExprCallTranslatorTests
{
    @Test
    public void quantifierDependsOnArgument() throws Exception
    {
        String alloy =
                "sig A {}\n" +
                "sig A0, A1 in A{}\n" +
                "pred disjointSets[u, v: A] {all x: u| some y: A-v | x & y = x}\n" +
                "fact {#A0 = 2 and #A1 = 2}\n" +
                "run {disjointSets[A0, A1]} for 4\n";

        List<CommandResult> commandResults = AlloyUtils.runAlloyString(alloy, false);

        assertEquals("sat", commandResults.get(0).satResult);

        FunctionDefinition a0 = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A0");
        Set<String> a0Atoms = TranslatorUtils.getAtomSet(a0);
        assertEquals(2, a0Atoms.size());

        FunctionDefinition a1 = AlloyUtils.getFunctionDefinition(commandResults.get(0), "this/A1");
        Set<String> a1Atoms = TranslatorUtils.getAtomSet(a1);
        assertEquals(2, a1Atoms.size());

        assertTrue(Collections.disjoint(a0Atoms, a1Atoms));
    }
}
