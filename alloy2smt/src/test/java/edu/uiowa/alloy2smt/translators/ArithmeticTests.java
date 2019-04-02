package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

public class ArithmeticTests
{
    @Test
    public void simple()
    {
        String alloy =
                "sig a, b, c in Int {}\n" +
                "\n" +
                "fact {\n" +
                "#a = 1\n" +
                "#b = 1\n" +
                "plus[a, b] = 2\n" +
                "plus[c, 0] = 2\n" +
                "}\n";
        Translation translation = Utils.translate(alloy);
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void testPlusMinus()
    {
        String alloy =
                "sig a, b, c, d in Int {}\n" +
                "fact add{plus[a,b] = c + d}\n" +
                "fact subtract{minus[a,b] = c - d}\n" +
                "fact notEqual{a != c and b != d}\n" +
                "fact nonzero {a > 0 and b > 0 and c > 0 and d > 0}\n";
        Translation translation = Utils.translate(alloy);

        Assertions.assertTrue(translation.getSmtScript().contains(
                "(declare-fun intUniv"));
    }
}
