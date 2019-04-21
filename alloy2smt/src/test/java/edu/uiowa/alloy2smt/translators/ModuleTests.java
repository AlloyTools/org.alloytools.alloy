package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smt.TranslatorUtils;
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
                "fact f {#A = 3 and #B = 4 and some ordB/prev}\n" +
                "run {} for 10 but 3 A, 4 B\n";

        Translation translation = Utils.translate(alloy);

        String script = translation.getSmtScript();

        Assertions.assertTrue(script.contains("(declare-fun ordA_Ord"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_Ord_First"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_Ord_Next"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_IntMap"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_first"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_last"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_next"));
        Assertions.assertTrue(script.contains("(declare-fun ordA_prev"));
        Assertions.assertTrue(script.contains("(define-fun ordA_prevs"));
        Assertions.assertTrue(script.contains("(define-fun ordA_nexts"));
        Assertions.assertTrue(script.contains("(define-fun ordA_lt"));
        Assertions.assertTrue(script.contains("(define-fun ordA_gt"));
        Assertions.assertTrue(script.contains("(define-fun ordA_lte"));
        Assertions.assertTrue(script.contains("(define-fun ordA_gte"));
        Assertions.assertTrue(script.contains("(define-fun ordA_larger"));
        Assertions.assertTrue(script.contains("(define-fun ordA_smaller"));
        Assertions.assertTrue(script.contains("(define-fun ordA_max"));
        Assertions.assertTrue(script.contains("(define-fun ordA_min"));

        Assertions.assertTrue(script.contains("(declare-fun ordB_Ord"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_Ord_First"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_Ord_Next"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_IntMap"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_first"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_last"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_next"));
        Assertions.assertTrue(script.contains("(declare-fun ordB_prev"));
        Assertions.assertTrue(script.contains("(define-fun ordB_prevs"));
        Assertions.assertTrue(script.contains("(define-fun ordB_nexts"));
        Assertions.assertTrue(script.contains("(define-fun ordB_lt"));
        Assertions.assertTrue(script.contains("(define-fun ordB_gt"));
        Assertions.assertTrue(script.contains("(define-fun ordB_lte"));
        Assertions.assertTrue(script.contains("(define-fun ordB_gte"));
        Assertions.assertTrue(script.contains("(define-fun ordB_larger"));
        Assertions.assertTrue(script.contains("(define-fun ordB_smaller"));
        Assertions.assertTrue(script.contains("(define-fun ordB_max"));
        Assertions.assertTrue(script.contains("(define-fun ordB_min"));
    }
}
