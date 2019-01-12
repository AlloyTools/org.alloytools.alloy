package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.mapping.MappingSignature;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

public class IntSigTranslationTests
{
    @Test
    public void intSignatures1()
    {
        String alloy =
                "sig A0, A1, A2 in Int {}\n" +
                "fact {A0 = 1 and A1 = 2 and A2 = 3}\n";
        Translation translation = Utils.translate(alloy);
        Assertions.assertEquals(5, translation.getMapper().signatures.size());


        MappingSignature Int = translation.getMapper().signatures
                .stream().filter(s -> s.label.equals("Int")).findFirst().get();

        MappingSignature A0 = translation.getMapper().signatures
                .stream().filter(s -> s.label.contains("A0")).findFirst().get();
        MappingSignature A1 = translation.getMapper().signatures
                .stream().filter(s -> s.label.contains("A1")).findFirst().get();
        MappingSignature A2 = translation.getMapper().signatures
                .stream().filter(s -> s.label.contains("A2")).findFirst().get();

        Assertions.assertEquals(Int.id, A0.parents.get(0));
        Assertions.assertEquals(Int.id, A1.parents.get(0));
        Assertions.assertEquals(Int.id, A2.parents.get(0));
    }

    @Test
    public void intSignatures2()
    {
        String alloy =
                "sig A0, A1, A2 in Int {}\n" +
                "sig A4 in Int + A0+A1 {}\n" +
                "fact {A0 = 1 and A1 = 2 and A2 = 3}\n";
        Translation translation = Utils.translate(alloy);
        Assertions.assertTrue(translation.getSmtScript().contains(
                "(declare-fun intUniv"));
    }

    @Test
    public void intSignatures3()
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
