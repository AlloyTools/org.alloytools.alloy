package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class SampleModelTests
{
    private Translation getExample(String fileName) throws IOException
    {
        String content = new String(Files.readAllBytes(Paths.get(fileName)));
        Translation translation = Utils.translate(content);
        return translation;
    }

    @Test
    public void farmer() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als");

        String script = translation.translateAllCommandsWithCheckSat();

        Assertions.assertTrue(script.contains("(declare-const ord_next"));
        Assertions.assertTrue(script.contains("(declare-const ord_last"));
    }

    @Test
    public void abstractMemory() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/abstractMemory.als");

        String writeIdempotent =  translation.translateCommand(1);

        Assertions.assertFalse(writeIdempotent.contains("m\""));
    }

    @Test
    public void cacheMemory() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/cacheMemory.als");
        // ToDo: fix the exception thrown by the next expression: by supporting setof operator
        //  "set c . (this/CacheSystem <: main) . this/Data - c . (this/CacheSystem <: cache) . this/Data"
    }

    @Test
    public void hotel1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel1.als");
        // ToDo: support multiplicity constraints on relations with arity GT 3!
    }

    @Test
    public void messaging() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als");
        // ToDo: support ONE_ARROW_ONE
    }

    @Test
    public void ringlead() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als");
        // ToDo: support # needsToSend = # { m: reads | m.state.id in nodeOrd/nexts[self] }
    }

    @Test
    public void stable_mutex_ring() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als");
        // ToDo: support ONE_ARROW_ONE
    }

    @Test
    public void firewire() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als");
        // ToDo: support LONE_ARROW_ANY
    }
}
