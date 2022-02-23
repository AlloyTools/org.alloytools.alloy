package org.alloytools.alloy.classic.test;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.HashSet;
import java.util.Set;

import org.alloytools.alloy.classic.provider.AlloyClassicFacade;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IAtom;
import org.junit.Test;


public class SpectTest {

    Alloy  alloy  = new AlloyClassicFacade();
    Spec   spec   = new Spec(alloy);

    //@formatter:off
    String source = "      enum bool { false, true }\n"
                    + "    let tob[a] = (a)=> true else false\n"
                    + "    sig Foo {}\n"
                    + "\n"
                    + "    pred add[ d,dd : set Foo, m : Foo, ans : bool ] {\n"
                    + "        dd = d+m\n"
                    + "        ans = tob[m not in d]\n"
                    + "    }\n"
                    + "\n"
                    + "    pred remove[ d,dd : set Foo, m : Foo, ans : bool ] {\n"
                    + "        dd = d-m\n"
                    + "        ans = tob[m in d]\n"
                    + "    }\n"
                    + "\n"
                    + "    pred clear[ d, dd : set Foo ] {\n"
                    + "        no dd\n"
                    + "    }\n"
                    + "\n";
    //@formatter:on


    public static class SetTest {

        public <T> void add(Set<T> d, Set<T> dd, T m, boolean ans) {

            HashSet<T> result = new HashSet<>(d);
            assertThat(result).isEqualTo(d);

            boolean add = result.add(m);

            assertThat(result).isEqualTo(dd);
            assertThat(add).isEqualTo(ans);
        }

        public void remove(Set<IAtom> d, Set<IAtom> dd, IAtom m, boolean ans) {
            HashSet<IAtom> result = new HashSet<>(d);
            assertThat(result).isEqualTo(d);

            boolean remove = result.remove(m);

            assertThat(result).isEqualTo(dd);
            assertThat(remove).isEqualTo(ans);
        }

        public void clear(Set<IAtom> d, Set<IAtom> dd) {
            HashSet<IAtom> result = new HashSet<>(d);
            assertThat(result).isEqualTo(d);

            result.clear();

            assertThat(result).isEqualTo(dd);
        }

    }

    @Test
    public void testSpec() throws Throwable {
        System.out.println(spec);
        spec.registerType("false", () -> false);
        spec.registerType("true", () -> true);
        spec.debug();
        spec.test(source, new SetTest());
    }

}
