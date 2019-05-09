package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class GeneralTests
{
    @Test
    public void test1()
    {
        String alloy =  "sig A {r: A -> A}\n" +
                "\n" +
                "fact {\n" +
                "#r = 2\n" +
                "}\n" +
                "run {} for 4 Int, 7 seq";

        Translation translation = Utils.translate(alloy);

        String script = translation.getSmtScript();
    }
}
