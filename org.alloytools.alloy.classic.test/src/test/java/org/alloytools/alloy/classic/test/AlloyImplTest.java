package org.alloytools.alloy.classic.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.alloytools.alloy.classic.provider.AlloyClassicFacade;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.ITupleSet;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.AlloySolver;
import org.junit.Test;
import java.util.ArrayList;

public class AlloyImplTest {
	Alloy ai = new AlloyClassicFacade();

	@Test
	public void testSolvers() {
		System.out.println(ai.getSolvers());
		assertTrue(ai.getSolvers().size() > 0);

		assertNotNull(ai.getSolver("sat4j"));
		assertNotNull(ai.getSolver("minisat(jni)"));
	}

	@Test
	public void testSolversAll() {
		AlloyModule module = ai.compiler().compileSource("run { 1 = 1 }");

		for (TRun run : module.getRuns()) {
			for (AlloySolver solver : ai.getSolvers()) {
				AlloySolution solution = solver.run(module, null, run);
				assertTrue( solution.iterator().hasNext());
			}
		}
	}

	@Test
	public void simple() throws Exception {
		AlloyModule module = ai.compiler()
				.compileSource("some sig B {}\n" + "some sig A {  x : \"abc\" } \n" + "run Foo2 { #A =1 } for 2");
		assertNotNull(module);
		System.out.println("Sigs " + module.getSigs());
		System.out.println("Runs " + module.getRuns());

		AlloySolver solver = ai.getSolvers().get(0);
		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, null, run);

			for (AlloyInstance instance : solution) {

				for (TSig sig : module.getSigs()) {
					System.out.println(sig + "\t" + instance.getAtoms(sig));
					for (TField field : sig.getFields()) {
						System.out.println("\t" + field.getName() + " " + instance.getField(field));
					}
				}
			}
		}
	}

	@Test
	public void expects() throws Exception {
		Alloy ai = new AlloyClassicFacade();
		AlloyModule module = ai.compiler().compileSource(//
				"pred foo[x, y, z: Int] {" //
						+ " x < 5 and y < 5\n" //
						+ " x.add[y] = z and x > y and z < x" //
						+ "} "//
						+ "run foo for 5 int");

		AlloySolver solver = ai.getSolvers().get(0);

		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, null, run);

			for (AlloyInstance instance : solution) {
				int x = instance.getVariable(run.getName(), "x").scalar().toInt();
				int y = instance.getVariable(run.getName(), "y").scalar().toInt();
				int z = instance.getVariable(run.getName(), "z").scalar().toInt();
				System.out.println("x+y=z : " + x + "+" + y + "=" + z);
				assertEquals(z, x + y);
			}
		}
	}

	@Test
	public void sortedOutput() throws Exception {
		Alloy ai = new AlloyClassicFacade();
		AlloyModule module = ai.compiler().compileSource("some sig B {}\nrun { #B =9 } for 16");

		AlloySolver solver = ai.getSolvers().get(0);
		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, null, run);
			// TSig B = module.getSig("B").get();

			for (AlloyInstance instance : solution) {
				System.out.println(solution.none());
				System.out.println(instance.universe());
				System.out.println(instance.ident());
			}
		}
	}

	@Test
	public void commands() throws Exception {
		Alloy ai = new AlloyClassicFacade();
		AlloyModule module = ai.compiler().compileSource("some sig B {}");

		AlloySolver solver = ai.getSolvers().get(0);

		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, null, run);

			TSig B = module.getSig("B").get();
			TSig univ = module.getSig("univ").get();

			for (AlloyInstance instance : solution) {
				System.out.println(instance.getAtoms(univ));
				System.out.println(instance.getAtoms(B));
			}
		}
	}

	@Test
	public void iterator() throws Exception {
		Alloy ai = new AlloyClassicFacade();
		AlloyModule module = ai.compiler().compileSource("some sig B {}\n run show{} for 3");
		AlloySolver solver = ai.getSolvers().get(0);
		TRun run = module.getRuns().get(0);
		AlloySolution solution = solver.run(module, null, run);
		TSig B = module.getSig("B").get();

		ArrayList<Integer> atom_counts = new ArrayList();
		for (AlloyInstance instance : solution) {
                  System.out.println(instance.getAtoms(B));
			atom_counts.add(instance.getAtoms(B).size());
		}

		//We should see three solutions (one B atom, two B atoms, three B atoms)
		assertEquals(3, atom_counts.size());
		assert(atom_counts.contains(1));
		assert(atom_counts.contains(2));
		assert(atom_counts.contains(3));
	}

	@Test
	public void iteratorImmutable() throws Exception {
		Alloy ai = new AlloyClassicFacade();
		AlloyModule module = ai.compiler().compileSource("some sig B {}\n run show{} for 3");
		AlloySolver solver = ai.getSolvers().get(0);
		TRun run = module.getRuns().get(0);
		AlloySolution solution = solver.run(module, null, run);
		TSig B = module.getSig("B").get();

		//Advancing the iterator shouldn't change previously returned instances.
		//Test this by comparing atoms between instances from an exhausted iterator with instances from an in-progress iterator.
		ArrayList<AlloyInstance> instances = new ArrayList();
		for(AlloyInstance instance : solution) {
			instances.add(instance);
		}

		int i = 0;
		for(AlloyInstance instance : solution) {
			ITupleSet ts = instance.getAtoms(B);
			ITupleSet ts_old = instances.get(i).getAtoms(B);
			//Comparing strings since value-based equality isn't implemented for tuple sets
			assertEquals(ts.toString(), ts_old.toString());
			i++;
		}
	}
}
