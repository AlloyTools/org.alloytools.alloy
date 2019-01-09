package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.Test;

public class IntSigTranslationTests
{
    @Test
    public void intSignatures()
    {
        String alloy =
                "sig A in Int {}\n" +
                "sig B in Int {}\n" +
                "fact {plus[A,B] = 5}";

        Translation translation = Utils.translate(alloy);
    }

    @Test
    public void remainder()
    {
        String alloy =
                "sig A in Int{}\n" +
                "sig B in Int{}\n" +
                "fact{rem[A, B] = 1}";
        Translation translation = Utils.translate(alloy);
    }
}
