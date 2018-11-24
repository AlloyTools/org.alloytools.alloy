package org.alloytools.alloy.core;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class AlloyModelsPartialInstancesTest {

    final String TEST_FILE       = "/Users/vajih/Documents/workspace-git/org.alloytools.alloy/org.alloytools.alloy.core/src/test/resources/test-partial-instances.als";
    final String DEFAULT_COMMAND = "for default_bound";

    protected Module loadTestFile(final String commandName) throws FileNotFoundException, IOException {
        String content = Util.readAll(TEST_FILE).replace(DEFAULT_COMMAND, "for " + commandName);
        System.out.println(content);
        return CompUtil.parseEverything_fromString(A4Reporter.NOP, content);
    }

    protected Sig findSig(SafeList<Sig> sigs, String label) {
        return sigs.makeCopy().stream().filter(s -> s.label.equals("this/" + label)).findAny().orElseThrow(() -> new RuntimeException("sig " + label + " is not found"));
    }

    @Test
    public void testExactBound() throws Exception {
        final Module world = loadTestFile("exact_bound");
        final A4Options options = new A4Options();
        final Command command = world.getAllCommands().get(0);
        final A4Solution ans = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), command, options);

        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 2);
    }
}
