package org.alloytools.alloy.core.provider;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import org.alloytools.alloy.control.api.Alloy;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.AlloySolver;
import org.junit.Test;

public class AlloyImplTest {

	@Test
	public void simple() throws Exception {
		Alloy ai = new AlloyImpl();
		AlloyModule module = ai.compiler()
				.compileSource("some sig B {}\n" + "some sig A {  x : \"abc\" } \n" + "run Foo2 { #A =1 } for 2");
		assertNotNull(module);
		System.out.println("Sigs " + module.getSigs());
		System.out.println("Runs " + module.getRuns());

		AlloySolver solver = ai.getDefaultSolver();
		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, run);

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
		Alloy ai = new AlloyImpl();
		AlloyModule module = ai.compiler().compileSource("pred foo[x, y, z: Int] { x.add[y] = z and x > y and z < x} run foo");

		AlloySolver solver = ai.getDefaultSolver();

		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, run);

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
		Alloy ai = new AlloyImpl();
		AlloyModule module = ai.compiler().compileSource("some sig B {}\nrun { #B =9 } for 16");

		AlloySolver solver = ai.getDefaultSolver();
		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, run);
			TSig B = module.getSig("B").get();

			for (AlloyInstance instance : solution) {
				System.out.println(solution.none());
				System.out.println(instance.universe());
				System.out.println(instance.ident());
			}
		}
	}

	@Test
	public void commands() throws Exception {
		Alloy ai = new AlloyImpl();
		AlloyModule module = ai.compiler().compileSource("some sig B {}");

		AlloySolver solver = ai.getDefaultSolver();

		for (TRun run : module.getRuns()) {

			AlloySolution solution = solver.run(module, run);

			TSig B = module.getSig("B").get();
			TSig univ = module.getSig("univ").get();

			for (AlloyInstance instance : solution) {
				System.out.println(instance.getAtoms(univ));
				System.out.println(instance.getAtoms(B));
			}
		}
	}
}
