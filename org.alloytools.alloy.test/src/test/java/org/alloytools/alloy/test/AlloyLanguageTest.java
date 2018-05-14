package org.alloytools.alloy.test;

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
import org.alloytools.alloy.core.api.AlloyCompiler;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.AlloySolver;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import aQute.lib.io.IO;

@RunWith(Parameterized.class)
public class AlloyLanguageTest {

	Alloy				alloy;
	AlloyModule			module;
	TRun				run;
	private AlloySolver	solver;
	private String		name;

	@Parameters(name="{index} {0} {3} {4}")
	public static Collection<Object[]> createData() {

		List<Object[]> result = new ArrayList<>();

		File[] testFiles = IO.getFile("src/main/resources").listFiles();
		List<Alloy> alloys = Services.getServices(Alloy.class);

		for (File f : testFiles) {
			for (Alloy alloy : alloys) {
				alloy.getSolvers();
				AlloyCompiler compiler = alloy.compiler();
				AlloyModule module = compiler.compile(f);
				if (module == null) {
					System.out.println(f);
				}
				if (!module.isValid()) {
					fail("Compile failed for " + f.getName() + " " + module.getErrors());
				}
				assertTrue(f.getPath(), module.isValid());
				for (AlloySolver solver : alloy.getSolvers()) {
					for (TRun run : module.getRuns()) {
						result.add(new Object[] { f.getName(), alloy, module, run, solver });
					}
				}
			}
		}
		return result;
	}

	public AlloyLanguageTest(String name, Alloy alloy, AlloyModule module, TRun run, AlloySolver solver)
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
		AlloySolution solution = solver.run(module, null, run);
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
				break;
			}
		} finally {
			System.out.printf("%-20s %-20s %12s %-5s %-12s: %s %s\n", name, solver,
					DTOs.readableTime(System.currentTimeMillis() - now), solution.isSatisfied(), run.getExpects(),
					module.getSourceOptions(run), run);
		}
	}

}
