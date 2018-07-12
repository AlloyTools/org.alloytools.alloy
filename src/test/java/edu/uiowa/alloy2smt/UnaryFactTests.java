package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


class UnaryFactTests extends TestBase
{
    @Test
    public void no1()
    {
        String input =
                "sig A {}\n" +
                "fact f {no A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (forall ((_x1 Atom)) (not (member (mkTuple _x1 ) this_A))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void no2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {no B.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "; f\n" +
                "(assert (forall ((_x1 Atom)) (not (member (mkTuple _x1 ) (join this_B this_B_r)))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void all1()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {all b : B | no b.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "; f\n" +
                "(assert (forall ((b Atom)) " +
                        "(=> (member (mkTuple b ) this_B) " +
                            "(forall ((_x1 Atom)) " +
                                "(not (member " +
                                    "(mkTuple _x1 ) " +
                                        "(join (singleton (mkTuple b )) this_B_r)))))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void all2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {" +
                "all b : B | all a : A | no b.r + a" +
                "}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                        "(assert (subset this_B_r (product this_B this_A)))\n" +
                        "; f\n" +
                        "(assert (forall ((b Atom)) " +
                            "(=> (member (mkTuple b ) this_B) " +
                                "(forall ((a Atom)) " +
                                    "(=> (member (mkTuple a ) this_A) " +
                                        "(forall ((_x1 Atom)) " +
                                            "(not (member (mkTuple _x1 ) " +
                                                    "(union " +
                                                            "(join (singleton (mkTuple b )) this_B_r) " +
                                                    "(singleton (mkTuple a )))))))))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void all3()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {" +
                "all b : B | no b.r \n" +
                "all b : A | no r.b" + // reuse bound variable b
                "}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "; f\n" +
                "(assert (and " +
                        "(forall ((b Atom)) (=> (member (mkTuple b ) this_B) " +
                            "(forall ((_x1 Atom)) (not (member (mkTuple _x1 ) (join (singleton (mkTuple b )) this_B_r)))))) " +
                        "(forall ((b Atom)) (=> (member (mkTuple b ) this_A) " +
                            "(forall ((_x2 Atom)) (not (member (mkTuple _x2 ) (join this_B_r (singleton (mkTuple b ))))))))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void some1()
    {
        String input =
                "sig A {}\n" +
                "fact f {some A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (exists ((_x1 Atom)) (member (mkTuple _x1 ) this_A)))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void some2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {some B.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "; f\n" +
                "(assert (exists ((_x1 Atom)) (member (mkTuple _x1 ) (join this_B this_B_r))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void one1()
    {
        String input =
                "sig A {}\n" +
                "fact f {one A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (exists ((_x1 Atom)) " +
                    "(and (member (mkTuple _x1 ) this_A) " +
                        "(forall ((_x2 Atom)) " +
                            "(=> (not (= _x1 _x2)) (not (member (mkTuple _x2 ) this_A)))))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void one2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {one B.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_B_r (product this_B this_A)))\n" +
                "; f\n" +
                "(assert (exists ((_x1 Atom)) " +
                    "(and " +
                        "(member (mkTuple _x1 ) (join this_B this_B_r)) " +
                        "(forall ((_x2 Atom)) (=> (not (= _x1 _x2)) " +
                            "(not (member (mkTuple _x2 ) (join this_B this_B_r))))))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void lone1()
    {
        String input =
                "sig A {}\n" +
                "fact f {lone A}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "; f\n" +
                "(assert (or " +
                            "(exists ((_x1 Atom)) " +
                                "(and (member (mkTuple _x1 ) this_A) " +
                                    "(forall ((_x2 Atom)) (=> (not (= _x1 _x2)) " +
                                        "(not (member (mkTuple _x2 ) this_A)))))) " +
                            "(forall ((_x3 Atom)) (not (member (mkTuple _x3 ) this_A)))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void lone2()
    {
        String input =
                "sig A {}\n" +
                "sig B {r: set A}\n" +
                "fact f {lone B.r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                    "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                    "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                    "(assert (subset this_B_r (product this_B this_A)))\n" +
                    "; f\n" +
                    "(assert (or " +
                                "(exists ((_x1 Atom)) " +
                                    "(and (member (mkTuple _x1 ) (join this_B this_B_r)) " +
                                    "(forall ((_x2 Atom)) (=> (not (= _x1 _x2)) " +
                                        "(not (member (mkTuple _x2 ) (join this_B this_B_r))))))) " +
                            "(forall ((_x3 Atom)) (not (member (mkTuple _x3 ) " +
                                                    "(join this_B this_B_r))))))\n";
        assertEquals(expected, actual);
    }


    @Test
    public void transpose()
    {
        String input =
                "sig A {}\n" +
                "sig B{r : set A}\n" +
                "fact f {some ~r.B }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                        "(assert (subset this_B_r (product this_B this_A)))\n" +
                        "; f\n" +
                        "(assert (exists ((_x1 Atom)) (member (mkTuple _x1 ) (join (transpose this_B_r) this_B))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void closure1()
    {
        String input =
                "sig A {r : set A}\n" +
                "fact f {some ^r}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A_r () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_A_r (product this_A this_A)))\n" +
                "; f\n" +
                "(assert (exists ((_x1 Atom)(_x2 Atom)) (member (mkTuple _x1 _x2 ) (tclosure this_A_r))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void closure2()
    {
        String input =
                "sig A {r1 : set A, r2: set A}\n" +
                "fact f { some ^(r1.r2)}\n" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_A_r () (Set (Tuple Atom Atom )))\n" +
                        "(assert (subset this_A_r (product this_A this_A)))\n" +
                        "; f\n" +
                        "(assert (exists ((_x1 Atom)(_x2 Atom)) (member (mkTuple _x1 _x2 ) (tclosure this_A_r))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void reflexiveClosure1()
    {
        String input =
                "sig A {r : set A}\n" +
                "fact f {some *r }";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_B_r () (Set (Tuple Atom Atom )))\n" +
                        "(assert (subset this_B_r (product this_B this_A)))\n" +
                        "; f\n" +
                        "(assert (exists ((_x1 Atom)) (member (mkTuple _x1 ) (join (transpose this_B_r) this_B))))\n";
        assertEquals(expected, actual);
    }

}