package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.smtAst.SMTAst;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


class Alloy2SMTTranslatorTest
{
    @Test
    public void executeSimpleModel()
    {

        String input = "sig Name, Addr {}\n" +
                        "sig Book {\n" +
                            "addr: Name -> lone Addr\n" +
                        "}\n" +
                        "\n" +
                        "pred show () {}\n" +
                        "run show for 3 but 1 Book";

        String actual = Utils.translateFromString(input);
        String expected = "?";
        assertEquals(expected, actual);
    }
}