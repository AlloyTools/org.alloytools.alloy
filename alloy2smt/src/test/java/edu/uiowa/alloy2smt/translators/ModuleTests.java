package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class ModuleTests
{
    @Test
    void ordModule1()
    {
        String alloy =
                "open util/ordering[A] as ordA\n" +
                "open util/ordering[B] as ordB\n" +
                "sig A {}\n" +
                "sig B {}\n" +
                "fact f {#A = 3 and #B = 4}\n" +
                "run {} for 10 but 3 A, 4 B\n";

        Translation translation = Utils.translate(alloy);

        Assertions.assertTrue(translation.getSmtScript().contains(
                "; last element is a member of this/B\n" +
                        "(assert (member (mkTuple _a2) this_B))\n" +
                        "; ordB/Ord . (ordB/Ord <: First)\n" +
                        "(assert (= (singleton (mkTuple _a1)) (join ordB_Ord ordB_Ord_First)))\n" +
                        "; No predecessor before _a1\n" +
                        "(assert (= (as emptyset (Set (Tuple Atom))) (join (join ordB_Ord ordB_Ord_Next) (singleton (mkTuple _a1)))))\n" +
                        "; No successor after _a2\n" +
                        "(assert (= (as emptyset (Set (Tuple Atom))) (join (singleton (mkTuple _a2)) (join ordB_Ord ordB_Ord_Next))))\n" +
                        "; Each element except the first element has exactly one predecessor\n" +
                        "(assert (forall ((_a3 Atom)) (=> (and (member (mkTuple _a3) this_B) (not (= _a1 _a3))) (exists ((_a4 Atom)) (= (singleton (mkTuple _a4)) (join (join ordB_Ord ordB_Ord_Next) (singleton (mkTuple _a3))))))))\n" +
                        "; Each element except the last element has exactly one successor\n" +
                        "(assert (forall ((_a3 Atom)) (=> (and (member (mkTuple _a3) this_B) (not (= _a2 _a3))) (exists ((_a4 Atom)) (= (singleton (mkTuple _a4)) (join (singleton (mkTuple _a3)) (join ordB_Ord ordB_Ord_Next)))))))\n" +
                        "; last element is a member of this/A\n" +
                        "(assert (member (mkTuple _a6) this_A))\n" +
                        "; ordA/Ord . (ordA/Ord <: First)\n" +
                        "(assert (= (singleton (mkTuple _a5)) (join ordA_Ord ordA_Ord_First)))\n" +
                        "; No predecessor before _a5\n" +
                        "(assert (= (as emptyset (Set (Tuple Atom))) (join (join ordA_Ord ordA_Ord_Next) (singleton (mkTuple _a5)))))\n" +
                        "; No successor after _a6\n" +
                        "(assert (= (as emptyset (Set (Tuple Atom))) (join (singleton (mkTuple _a6)) (join ordA_Ord ordA_Ord_Next))))\n" +
                        "; Each element except the first element has exactly one predecessor\n" +
                        "(assert (forall ((_a7 Atom)) (=> (and (member (mkTuple _a7) this_A) (not (= _a5 _a7))) (exists ((_a8 Atom)) (= (singleton (mkTuple _a8)) (join (join ordA_Ord ordA_Ord_Next) (singleton (mkTuple _a7))))))))\n" +
                        "; Each element except the last element has exactly one successor\n" +
                        "(assert (forall ((_a7 Atom)) (=> (and (member (mkTuple _a7) this_A) (not (= _a6 _a7))) (exists ((_a8 Atom)) (= (singleton (mkTuple _a8)) (join (singleton (mkTuple _a7)) (join ordA_Ord ordA_Ord_Next)))))))"));
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
