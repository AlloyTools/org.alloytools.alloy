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

        Assertions.assertTrue(translation.getSmtScript().contains("(define-fun ord_next"));
    }

    @Test
    public void abstractMemory() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/memory/abstractMemory.als");

        String writeIdempotent =  translation.translateCommand(1);

        Assertions.assertFalse(writeIdempotent.contains("m\""));
    }
}
