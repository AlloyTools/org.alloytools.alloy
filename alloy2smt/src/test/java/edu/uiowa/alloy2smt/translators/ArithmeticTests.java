package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

public class ArithmeticTests
{
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
