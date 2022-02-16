package org.alloytools.alloy.classic.test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import org.alloytools.alloy.classic.provider.AlloyClassicFacade;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solution.Trace;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSignature;
import org.junit.Test;

public class AlloyImplTest {

    Alloy  ai     = new AlloyClassicFacade();
    Solver solver = ai.getSolvers().get("");

    @Test
    public void testAtomNaming() {
        Solution s = ai.getSolution("sig Foo {} run { #Foo in 2+3}");

        Instance[] instances = s.next(4);
        assertThat(instances).hasSize(2);

        TSignature foo = s.getModule().getSignatures().get("Foo");

        IRelation atoms0 = instances[0].getAtoms(foo);
        IRelation atoms1 = instances[1].getAtoms(foo);
        assertThat(atoms0).hasSize(2);
        assertThat(atoms1).hasSize(3);

        assertThat(atoms0.in(atoms1)).isTrue();
        assertThat(atoms1.in(atoms0)).isFalse();

    }



    @Test
    public void testStandardNext() {
        Module module = ai.compiler().compileSource("one sig G { y : Int} { y in 0+1+2 } ");
        assertThat(module.getErrors()).isEmpty();
        Solution solve = solver.solve(module.getDefaultCommand(), null);
        List<Integer> l = new ArrayList<>();
        for (Instance instance : solve) {
            Object eval = instance.eval("G.y");
            assertThat(eval).isNotNull();
            IRelation r = (IRelation) eval;
            assertThat(r.isScalar()).isTrue();
            l.add(r.scalar().get().toInt());
        }
        assertThat(l).containsExactlyInAnyOrder(0, 1, 2);
    }

    /*
     * 2 static configurations, 4 traces, 2 possible traces
     */
    @Test
    public void testNextTraces() {

        Module module = ai.compiler().compileSource(//
                                                    "   one sig G { var x : Int, y : Int } { y in 0+1 }\n" //
                                                    + "    run { G.x=2 ; G.x=3 ; G.x=4 ; G.x=G.y }");
        assertThat(module.getErrors()).isEmpty();
        Solution solve = solver.solve(module.getDefaultCommand(), null);
        assertThat(solve.hasVariables()).isTrue();

        List<Instance> configurations = new ArrayList<>();
        for (Instance s : solve) {
            configurations.add(s);
            Object eval = s.eval("G.y");
            Iterator<Trace> cursor = solve.trace(s).iterator();

            Instance[] t0 = cursor.next().instances();
            Instance[] t1 = cursor.next().instances();

        }
        assertThat(configurations).hasSize(2);

    }


    //    @Test
    //    public void testSimpleTrace() {
    //
    //        for (TRun run : module.getRuns().values()) {
    //            for (Solver solver : ai.getSolvers()) {
    //                Solution solve = solver.solve(run, null);
    //                for (Instance root : solve) {
    //                    for (Trace trace : solve.trace(root)) {
    //                        Instance[] instances = trace.instances();
    //                        System.out.println(instances.length + " " + trace.loop());
    //                    }
    //
    //                }
    //            }
    //        }
    //
    //    }



    @Test
    public void testSolvers() {
        System.out.println(ai.getSolvers());
        assertTrue(ai.getSolvers().size() > 0);

        assertNotNull(ai.getSolvers().get("sat4j"));
        assertNotNull(ai.getSolvers().get("minisat(jni)"));
    }

    @Test
    public void testSolversAll() {
        Module module = ai.compiler().compileSource("run { 1 = 1 }");
        assertThat(module.getRuns()).isNotEmpty();
        assertThat(ai.getSolvers()).isNotEmpty();
        for (TRun run : module.getRuns().values()) {
            for (Solver solver : ai.getSolvers().values()) {
                Solution solution = solver.solve(run, null);
                assertThat(solution.isSatisfied());
                assertThat(solution.iterator().hasNext());
                solution.forEach(inst -> {
                    System.out.println("solution " + run + " " + inst);
                    System.out.println("val " + inst.eval("1=1"));

                });
            }
        }
    }

    @Test
    public void iteratorImmutable() throws Exception {
        Module module = ai.compiler().compileSource("some sig B {}\n run show{} for 3");
        TRun run = module.getRuns().values().iterator().next();
        Solution solution = solver.solve(run, null, null, null);
        TSignature B = module.getSignatures().get("B");

        List<List<IAtom>> older = atoms(solution, B);
        List<List<IAtom>> newer = atoms(solution, B);

        assertEquals(3, newer.size());
        assertEquals(3, older.size());

        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
                List<IAtom> olderList = older.get(i);
                List<IAtom> newerList = newer.get(i);
                if (i == j) {
                    assertEquals(olderList, newerList);
                } else {
                    assertFalse(!olderList.equals(newerList));
                }
            }
        }
    }

    private List<List<IAtom>> atoms(Solution solution, TSignature B) {
        return slurp(solution).stream().map(inst -> inst.getAtoms(B).asList()).collect(Collectors.toList());
    }

    private <T> List<T> slurp(Iterable<T> solution) {
        List<T> list = new ArrayList<>();
        solution.forEach(list::add);
        return list;
    }

    @Test
    public void iterator() throws Exception {
        Module module = ai.compiler().compileSource("pred two[y:Int] { y = 1 or y = 2 or y = 3 } run two ");

        for (TRun run : module.getRuns().values()) {

            Solution solution = solver.solve(run, null, null, null);
            TFunction two = solution.getModule().getFunctions().get("two");
            List<Integer> collect = new ArrayList<>();
            for (Instance inst : solution) {
                IRelation y = inst.getParameters(two).get("y");
                collect.add(y.toInt());
            }
            assertEquals(Arrays.asList(1, 2, 3), collect);
        }
    }

    @Test(
          expected = IllegalStateException.class )
    public void testIteratorNoElements() throws Exception {
        Module module = ai.compiler().compileSource("pred nothing[y:Int] { y = 1 and y = 2 } run nothing ");

        TRun run = module.getRuns().get("nothing");

        Solution solution = solver.solve(run, null, null, null);
        assertFalse(solution.isSatisfied());
        solution.iterator().next();
    }

    @Test
    public void simple() throws Exception {
        Module module = ai.compiler().compileSource("some sig B {}\n" + "some sig A {  x : \"abc\" } \n" + "run Foo2 { #A =1 } for 2");
        assertNotNull(module);
        System.out.println("Sigs " + module.getSignatures());
        System.out.println("Runs " + module.getRuns());

        for (TRun run : module.getRuns().values()) {

            Solution solution = solver.solve(run, null, null, null);

            for (Instance instance : solution) {

                for (TSignature sig : module.getSignatures().values()) {
                    System.out.println(sig + "\t" + instance.getAtoms(sig));
                    for (TField field : sig.getFieldMap().values()) {
                        System.out.println("\t" + field.getName() + " " + instance.getField(field));
                    }
                }
            }
        }
    }

    @Test
    public void expects() throws Exception {
        Alloy ai = new AlloyClassicFacade();
        Module module = ai.compiler().compileSource(//
                                                    "pred foo[x, y, z: Int] {" //
                                                    + " x < 5 and y < 5\n" //
                                                    + " x.add[y] = z and x > y and z < x" //
                                                    + "} "//
                                                    + "run foo for 5 int");

        for (TRun run : module.getRuns().values()) {

            Solution solution = solver.solve(run, null, null, null);

            for (Instance instance : solution) {
                int x = instance.getVariable(run.getName(), "x").scalar().orElseThrow(Exception::new).toInt();
                int y = instance.getVariable(run.getName(), "y").scalar().orElseThrow(Exception::new).toInt();
                int z = instance.getVariable(run.getName(), "z").scalar().orElseThrow(Exception::new).toInt();
                System.out.println("x+y=z : " + x + "+" + y + "=" + z);
                assertEquals(z, x + y);
            }
        }
    }

    @Test
    public void sortedOutput() throws Exception {
        Alloy ai = new AlloyClassicFacade();
        Module module = ai.compiler().compileSource("some sig B {}\nrun { #B =9 } for 16");

        for (TRun run : module.getRuns().values()) {

            Solution solution = solver.solve(run, null, null, null);
            // TSig B = module.getSig("B").get();

            for (Instance instance : solution) {
                System.out.println(solution.none());
                System.out.println(instance.eval("univ"));
                System.out.println(instance.eval("iden"));
            }
        }
    }

    @Test
    public void commands() throws Exception {
        Alloy ai = new AlloyClassicFacade();
        Module module = ai.compiler().compileSource("some sig B {}");

        for (TRun run : module.getRuns().values()) {

            Solution solution = solver.solve(run, null, null, null);
            System.out.println(module.getSignatures());
            TSignature B = module.getSignatures().get("B");
            TSignature univ = module.getSignatures().get("univ");

            for (Instance instance : solution) {
                System.out.println(instance.getAtoms(univ));
                System.out.println(instance.getAtoms(B));
            }
        }
    }
}
