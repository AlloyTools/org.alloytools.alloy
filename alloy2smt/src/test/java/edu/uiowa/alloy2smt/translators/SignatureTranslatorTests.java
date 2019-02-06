package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class SignatureTranslatorTests
{
    @Test
    void sigFacts()
    {
        String alloy = "sig A {}{some A}";
        Translation translation = Utils.translate(alloy);

        // sig facts should be true for each atom in the signature
        Assertions.assertTrue(translation.getSmtScript().contains(
                "; Fact for sig: this/A\n" +
                "(assert (forall ((this Atom)) (=> (member (mkTuple this) this_A) (exists ((_x1 Atom)) (member (mkTuple _x1) this_A)))))"));
    }
}




