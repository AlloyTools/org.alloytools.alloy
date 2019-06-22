package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.FunctionDefinition;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ModuleTests
{
    @BeforeEach
    void init()
    {
        TranslatorUtils.reset();
    }


    @Test
    public void ordModule1() throws Exception
    {
        String alloy =
                "open util/ordering[A] as ordA\n" +
                "open util/ordering[B] as ordB\n" +
                "sig A {}\n" +
                "sig B {}\n" +
                "fact f {#A = 3 and #B = 4}\n" +
                "run {} for 4 but 3 A, 4 B\n";

        List<CommandResult> results =  AlloyUtils.runAlloyString(alloy, false);
        assertEquals ("sat", results.get(0).satResult);
        FunctionDefinition a = AlloyUtils.getFunctionDefinition(results.get(0), "this/A");
        Set<String> aAtoms = TranslatorUtils.getAtomSet(a);
        assertEquals(3, aAtoms.size());

        FunctionDefinition b = AlloyUtils.getFunctionDefinition(results.get(0), "this/B");
        Set<String> bAtoms = TranslatorUtils.getAtomSet(b);
        assertEquals(4, bAtoms.size());
    }
}
