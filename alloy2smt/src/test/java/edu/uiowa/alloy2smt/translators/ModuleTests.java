package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class ModuleTests
{
    @BeforeEach
    void init()
    {
        TranslatorUtils.reset();
    }


    @Test
    public void ordModule1()
    {
        String alloy =
                "open util/ordering[A] as ordA\n" +
                "open util/ordering[B] as ordB\n" +
                "sig A {}\n" +
                "sig B {}\n" +
                "fact f {#A = 3 and #B = 4}\n" +
                "run {} for 10 but 3 A, 4 B\n";

        Translation translation = Utils.translate(alloy);

        System.out.println(translation.getSmtScript());

        Assertions.assertTrue(translation.getSmtScript().contains(
                ""));
    }

    @Test
    void ordModuleLT()
    {
        String alloy =
                "open util/ordering[A] as ordA\n" +
                "abstract sig A {}\n" +
                "sig A0 , A1, A2 extends A{}\n" +
                "fact f {lt[A0, A2] and lt[A0, A1]}\n" +
                "run {} for 10 but 3 A";
        Translation translation = Utils.translate(alloy);

        Assertions.assertTrue(translation.getSmtScript().contains("(define-fun ordA_lt"));
    }
}
