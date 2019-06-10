package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class SampleModelTests
{
    @Test
    public void farmer() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void abstractMemory() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/abstractMemory.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void cacheMemory() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/cacheMemory.als", true);

        assertEquals("unsat", results.get(0).satResult);
        // ToDo: fix the exception thrown by the next expression: by supporting setof operator
        //  "set c . (this/CacheSystem <: main) . this/Data - c . (this/CacheSystem <: cache) . this/Data"
    }


    @Test
    public void messaging() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void ringlead() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Test
    public void stable_mutex_ring() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void firewire() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("unsat", results.get(5).satResult);
        assertEquals("sat", results.get(6).satResult);
    }
}
