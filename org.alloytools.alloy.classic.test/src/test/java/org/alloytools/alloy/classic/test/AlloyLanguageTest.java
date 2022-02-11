package org.alloytools.alloy.classic.test;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.allotools.conversion.util.DTOs;
import org.allotools.services.util.Services;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TCommand;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import aQute.lib.io.IO;

@RunWith(Parameterized.class )
public class AlloyLanguageTest {

    Alloy          alloy;
    Module         module;
    TCommand       command;
    private Solver solver;
    private String name;

    @Parameters(
                name = "{index} {0} {3} {4}" )
    public static Collection<Object[]> createData() {

        List<Object[]> result = new ArrayList<>();

        File[] testFiles = IO.getFile("src/test/resources/alloy.tests").listFiles();
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
                for (Solver solver : alloy.getSolvers().values()) {
                    Set<TCommand> commands = new HashSet<>(module.getRuns().values());
                    commands.addAll(module.getChecks().values());
                    for (TCommand run : commands) {
                        result.add(new Object[] {
                                                 f.getName(), alloy, module, run, solver
                        });
                    }
                }
            }
        }
        return result;
    }

    public AlloyLanguageTest(String name, Alloy alloy, Module module, TCommand run, Solver solver) throws IOException {
        this.name = name;
        this.alloy = alloy;
        this.module = module;
        this.command = run;
        this.solver = solver;
    }

    @Test
    public void testAlloy() {
        long now = System.currentTimeMillis();
        Solution solution = solver.solve(command, null, null, null);
        try {
            switch (command.getExpects()) {
                case SATISFIABLE :
                    assertTrue(name + " - " + command + " was expecting a solution", solution.isSatisfied());
                    break;
                case UNSATISFIABLE :
                    assertTrue(name + " - " + command + " was not expecting a solution", !solution.isSatisfied());
                    break;
                default :
                case UNKNOWN :
                    fail();
                    break;
            }
        } finally {
            System.out.printf("%-20s %-5s:%-20s %-16s %-16s %-16s %-8s %-12s: %s %s\n", name, command.isCheck() ? "check" : "run", command.getName(), command.getExpects(), solver, DTOs.readableTime(System.currentTimeMillis() - now), solution.isSatisfied(), command.getExpects(), module.getSourceOptions(command), command.getExpression());
        }
    }

}
