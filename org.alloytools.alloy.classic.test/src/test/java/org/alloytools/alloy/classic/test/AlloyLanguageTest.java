package org.alloytools.alloy.classic.test;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.allotools.conversion.util.DTOs;
import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TRun;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import aQute.lib.io.IO;

@RunWith(Parameterized.class)
public class AlloyLanguageTest {

	Alloy				alloy;
	Module			module;
	TRun				run;
	private Solver	solver;
	private String		name;

	@Parameters(name="{index} {0} {3} {4}")
	public static Collection<Object[]> createData() {

		List<Object[]> result = new ArrayList<>();

		File[] testFiles = IO.getFile("src/test/resources/alloy.tests")
			.listFiles();
		List<Alloy> alloys = Services.getServices(Alloy.class);

		for (File f : testFiles) {
			for (Alloy alloy : alloys) {
				alloy.getSolvers();
				Compiler compiler = alloy.compiler();
				Module module = compiler.compile(f);
				if (module == null) {
					System.out.println("Is no module " + f);
					continue;
				}
				if (!module.isValid()) {
					fail("Compile failed for " + f.getName() + " " + module.getErrors());
				}
				assertTrue(f.getPath(), module.isValid());
				for (Solver solver : alloy.getSolvers()) {
					for (TRun run : module.getRuns()) {
						result.add(new Object[] { f.getName(), alloy, module, run, solver });
					}
				}
			}
		}
		return result;
	}

	public AlloyLanguageTest(String name, Alloy alloy, Module module, TRun run, Solver solver)
			throws IOException {
		this.name = name;
		this.alloy = alloy;
		this.module = module;
		this.run = run;
		this.solver = solver;
	}

	@Test
	public void testAlloy() {
		long now = System.currentTimeMillis();
		Solution solution = solver.solve(run, null, null);
		try {
			switch (run.getExpects()) {
			case SATISFIED:
				assertTrue(name + " - " + run + " was expecting a solution", solution.isSatisfied());
				break;
			case UNSATISFIED:
				assertTrue(name + " - " + run + " was not expecting a solution", !solution.isSatisfied());
				break;
			default:
			case UNKNOWN:
					fail();
				break;
			}
		} finally {
			System.out.printf("%-20s %-20s %12s %-5s %-12s: %s %s\n", name, solver,
					DTOs.readableTime(System.currentTimeMillis() - now), solution.isSatisfied(), run.getExpects(),
					module.getSourceOptions(run), run);
		}
	}

}
