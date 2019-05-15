package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class SampleModelTests
{
    @Test
    public void farmer() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als", true);
    }

    @Test
    public void abstractMemory() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/abstractMemory.als", true);
    }

    @Test
    public void cacheMemory() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/cacheMemory.als", true);
        // ToDo: fix the exception thrown by the next expression: by supporting setof operator
        //  "set c . (this/CacheSystem <: main) . this/Data - c . (this/CacheSystem <: cache) . this/Data"
    }

    @Test
    public void hotel1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel1.als", true);
        // ToDo: support multiplicity constraints on relations with arity GT 3!
    }

    @Test
    public void messaging() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als", true);
        // ToDo: support ONE_ARROW_ONE
    }

    @Test
    public void ringlead() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true);
        // ToDo: support # needsToSend = # { m: reads | m.state.id in nodeOrd/nexts[self] }
    }

    @Test
    public void stable_mutex_ring() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true);
        // ToDo: support ONE_ARROW_ONE
    }

    @Test
    public void firewire() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true);
        // ToDo: support LONE_ARROW_ANY
    }
}
