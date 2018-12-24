package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class ExprBinaryTranslatorTests
{

    @BeforeEach
    void setUp()
    {
        TranslatorUtils.reset();
    }

    @Test
    void cardinalityEquality()
    {
        String alloy = "sig A {} \n fact f {#A = 3}";
        String smt = Utils.translateFromString(alloy, null);
        System.out.println(smt);

        String assertion = "(assert (exists ((_a1 Atom)(_a2 Atom)(_a3 Atom)) (and (= this_A (insert (mkTuple _a2) (mkTuple _a3) (singleton (mkTuple _a1)))) (distinct _a1 _a2 _a3))))";
        Assertions.assertTrue(smt.contains(assertion));
    }

    @Test
    void cardinalityDisequality()
    {
        String alloy = "sig A {} \n fact f {#A != 3}";
        String smt = Utils.translateFromString(alloy, null);
        System.out.println(smt);

        String assertion = "(assert (not (exists ((_a1 Atom)(_a2 Atom)(_a3 Atom)) (and (= this_A (insert (mkTuple _a2) (mkTuple _a3) (singleton (mkTuple _a1)))) (distinct _a1 _a2 _a3)))))";
        Assertions.assertTrue(smt.contains(assertion));
    }
}