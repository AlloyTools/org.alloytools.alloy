package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class SampleModelTests
{
    private Translation getExample(String fileName) throws IOException
    {
        String content = Files.readString(Paths.get(fileName));
        Translation translation = Utils.translate(content);
        return translation;
    }

    @Test
    void farmer() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als");

        Assertions.assertTrue(translation.getSmtScript().contains("(define-fun ord_next"));
    }
}
