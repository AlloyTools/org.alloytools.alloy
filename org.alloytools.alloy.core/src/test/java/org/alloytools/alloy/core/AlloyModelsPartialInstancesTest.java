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

    final String TEST_FILE       = "src/test/resources/test-partial-instances.als";
    final String DEFAULT_COMMAND = "for default_bound";

    protected A4Solution executeTestFile(final String commandName) throws FileNotFoundException, IOException {
        final String content = Util.readAll(TEST_FILE).replace(DEFAULT_COMMAND, "for " + commandName);
        final Module world = CompUtil.parseEverything_fromString(A4Reporter.NOP, content);
        final A4Options options = new A4Options();
        final Command command = world.getAllCommands().get(0);
        return TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), command, options);
    }

    protected Sig findSig(SafeList<Sig> sigs, String label) {
        return sigs.makeCopy().stream().filter(s -> s.label.equals("this/" + label)).findAny().orElseThrow(() -> new RuntimeException("sig " + label + " is not found"));
    }

    @Test
    public void testExactBound() throws Exception {
        A4Solution ans = executeTestFile("exact_bound");
        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 2);
    }

    @Test
    public void testExactNamedBound() throws Exception {
        A4Solution ans = executeTestFile("exact_named_bound");
        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 0);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A").getFields().get(0)).size()), 1);
    }

    @Test
    public void testLowerBound() throws Exception {
        A4Solution ans = executeTestFile("lower_bound");
        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 2);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 0);
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "A").getFields().get(0)).size()) >= 1);
    }

    @Test
    public void testUpperBound() throws Exception {
        A4Solution ans = executeTestFile("upper_bound");
        assertTrue(ans.satisfiable());
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()) <= 2);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 0);
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "A").getFields().get(0)).size()) >= 1);
    }

    @Test
    public void testRangeBound() throws Exception {
        A4Solution ans = executeTestFile("range_bound");
        assertTrue(ans.satisfiable());
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()) <= 2);
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()) >= 1);
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()) <= 2);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 0);
        assertTrue((ans.eval(findSig(ans.getAllReachableSigs(), "A").getFields().get(0)).size()) >= 1);
    }

    @Test
    public void testContinuedBound() throws Exception {
        A4Solution ans = executeTestFile("continued_int_bound");
        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 0);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 0);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 0);
        assertEquals((ans.eval(Sig.SIGINT)).size(), 4);
    }

    @Test
    public void testSparseBound() throws Exception {
        A4Solution ans = executeTestFile("sparse_int_bound");
        assertTrue(ans.satisfiable());
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "A")).size()), 0);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "B")).size()), 0);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C")).size()), 1);
        assertEquals((ans.eval(findSig(ans.getAllReachableSigs(), "C").getFields().get(0)).size()), 3);
        assertEquals((ans.eval(Sig.SIGINT)).size(), 5);
    }
}
