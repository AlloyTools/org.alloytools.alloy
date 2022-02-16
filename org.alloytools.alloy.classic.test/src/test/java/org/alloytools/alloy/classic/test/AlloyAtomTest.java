package org.alloytools.alloy.classic.test;


import static org.assertj.core.api.Assertions.assertThat;

import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import org.alloytools.alloy.classic.provider.AlloyClassicFacade;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TFunction;
import org.junit.Test;

public class AlloyAtomTest {

    final Alloy ai = new AlloyClassicFacade();


    @Test
    public void testAtoms() {
        Solution s = ai.getSolution("sig Foo { disj a : some 1+2 } pred foo[ f : Foo ] { some f.a } run foo for 2");
        TField field = s.getModule().getSignatures().get("Foo").getField("a").get();

        Instance[] next = s.next(40);
        for (Instance inst : next) {
            System.out.println(inst.getVariables());
            IRelation a = inst.getField(field);
            assertThat(a).isNotNull();

            assertThat(a.union(a)).isEqualTo(a);
            assertThat(a.intersection(a)).isEqualTo(a);
            assertThat(a.in(a)).isTrue();
            assertThat(a.difference(a)).isEqualTo(s.none());

        }

        Stream.of(next).map(ins -> ins.eval("a")).forEach(System.out::println);


    }



    interface I {
    }

    interface II {

        Set<I> i();
    }

    interface Rot {

        Set<I> a();

        Set<I> b();

        Set<II> ab();
    }

    @Test
    public void testRelationOperations() {
        Solution s = ai.getSolution(//
                                    "sig I {} " + //
                                    "pred foo[ a, b, u, i, dab, dba, ab_b, ba_a, abh, bah, abt, bat  : set I, ab,ba: I->I, aba : I->I->I, abba : I->I->I->I] { " + //
                                    "u=a+b " + //
                                    "i=a&b " + //
                                    "dab=a-b " + //
                                    "dba=b-a " + //
                                    "ab=a->b " + //
                                    "ba=b->a " + //
                                    "ab_b=ab.b " + //
                                    "ba_a=ba.a " +//
                                    "bah=ba.univ " + //
                                    "abh=ab.univ " + //
                                    "bat=univ.ba " + //
                                    "abt=univ.ab " + //
                                    "aba=ab->a " + //
                                    "aba=ab->a " + //
                                    "abba=ab->ba " + //
                                    "} run foo for 5");
        System.out.println(s.getModule().getFunctions());
        TFunction foo = s.getModule().getFunctions().get("foo");
        assertThat(foo).isNotNull();
        Instance[] next = s.next(4000);
        System.out.println(next.length + " solutions");
        int n = 0;
        for (Instance inst : next) {
            Map<String,IRelation> parameters = inst.getParameters(foo);
            IRelation a = parameters.get("a");
            IRelation b = parameters.get("b");
            IRelation u = parameters.get("u");
            IRelation i = parameters.get("i");
            IRelation dab = parameters.get("dab");
            IRelation dba = parameters.get("dba");
            IRelation ab = parameters.get("ab");
            IRelation ba = parameters.get("ba");
            IRelation aba = parameters.get("aba");
            IRelation ab_b = parameters.get("ab_b");
            IRelation ba_a = parameters.get("ba_a");
            IRelation abh = parameters.get("abh");
            IRelation bah = parameters.get("bah");
            IRelation abt = parameters.get("abt");
            IRelation bat = parameters.get("bat");
            IRelation abba = parameters.get("abba");

            assertThat(a.union(b)).isEqualTo(u);
            assertThat(a.intersection(b)).isEqualTo(i);
            assertThat(a.difference(b)).isEqualTo(dab);
            assertThat(b.difference(a)).isEqualTo(dba);
            assertThat(a.product(b)).isEqualTo(ab);
            assertThat(b.product(a)).isEqualTo(ba);
            assertThat(a.product(b)).isEqualTo(ab);
            assertThat(ab.product(a)).isEqualTo(aba);
            assertThat(ab.join(b)).isEqualTo(ab_b);
            assertThat(ba.join(a)).isEqualTo(ba_a);
            assertThat(ab.head()).isEqualTo(abh);
            assertThat(ba.head()).isEqualTo(bah);
            assertThat(ab.tail()).isEqualTo(abt);
            assertThat(ba.tail()).isEqualTo(bat);
            if (!b.isEmpty() && !a.isEmpty()) {
                assertThat(ab.head()).isEqualTo(a);
                assertThat(abba.tail().tail()).isEqualTo(ba);
            }
        }
    }

    @Test
    public void testRelationOperationsInt() {
        Solution s = ai.getSolution(//
                                    "pred foo[ a, b, u, i, dab, dba, ab_b, ba_a, abh, bah, abt, bat  : set Int, ab,ba: Int->Int, aba : Int->Int->Int] { " + //
                                    "u=a+b " + //
                                    "i=a&b " + //
                                    "dab=a-b " + //
                                    "dba=b-a " + //
                                    "ab=a->b " + //
                                    "ba=b->a " + //
                                    "ab_b=ab.b " + //
                                    "ba_a=ba.a " +//
                                    "bah=ba.univ " + //
                                    "abh=ab.univ " + //
                                    "bat=univ.ba " + //
                                    "abt=univ.ab " + //
                                    "aba=ab->a " + //
                                    "aba=ab->a " + //
                                    "} run foo for 5");
        System.out.println(s.getModule().getFunctions());
        TFunction foo = s.getModule().getFunctions().get("foo");
        assertThat(foo).isNotNull();
        Instance[] next = s.next(40000);
        System.out.println(next.length + " solutions");
        int n = 0;
        for (Instance inst : next) {
            Map<String,IRelation> parameters = inst.getParameters(foo);
            IRelation a = parameters.get("a");
            IRelation b = parameters.get("b");
            IRelation u = parameters.get("u");
            IRelation i = parameters.get("i");
            IRelation dab = parameters.get("dab");
            IRelation dba = parameters.get("dba");
            IRelation ab = parameters.get("ab");
            IRelation ba = parameters.get("ba");
            IRelation aba = parameters.get("aba");
            IRelation ab_b = parameters.get("ab_b");
            IRelation ba_a = parameters.get("ba_a");
            IRelation abh = parameters.get("abh");
            IRelation bah = parameters.get("bah");
            IRelation abt = parameters.get("abt");
            IRelation bat = parameters.get("bat");

            assertThat(a.union(b)).isEqualTo(u);
            assertThat(a.intersection(b)).isEqualTo(i);
            assertThat(a.difference(b)).isEqualTo(dab);
            assertThat(b.difference(a)).isEqualTo(dba);
            assertThat(a.product(b)).isEqualTo(ab);
            assertThat(b.product(a)).isEqualTo(ba);
            assertThat(a.product(b)).isEqualTo(ab);
            assertThat(ab.product(a)).isEqualTo(aba);
            assertThat(ab.join(b)).isEqualTo(ab_b);
            assertThat(ba.join(a)).isEqualTo(ba_a);
            assertThat(ab.head()).isEqualTo(abh);
            assertThat(ba.head()).isEqualTo(bah);
            assertThat(ab.tail()).isEqualTo(abt);
            assertThat(ba.tail()).isEqualTo(bat);
            if (!b.isEmpty() && !a.isEmpty()) {
                assertThat(ab.head()).isEqualTo(a);
            }
        }
    }

}
