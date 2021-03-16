package org.sat4j;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ISolver;

public class CLITest {

    @Test
    public void test01DecisionModeSAT() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-yes-ok.cnf" };
        launcher.run(args);
        assertEquals(ExitCode.SATISFIABLE, launcher.getExitCode());
    }

    @Test
    public void test02DecisionModeUNSAT() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-no-ok.cnf" };
        launcher.run(args);
        assertEquals(ExitCode.UNSATISFIABLE, launcher.getExitCode());
    }

    @Test
    public void test04MUSLauncher() {
        MUSLauncher launcher = new MUSLauncher();
        String[] args = { "src/test/testfiles/aim-50-no-ok.cnf" };
        launcher.run(args);
        assertEquals(ExitCode.UNSATISFIABLE, launcher.getExitCode());
    }

    @Test
    public void test05DecisionModeUNSATPROOF() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-no-ok.cnf" };
        System.setProperty("UNSATPROOF", "true");
        launcher.run(args);
        assertEquals(ExitCode.UNSATISFIABLE, launcher.getExitCode());
        assertTrue(new File(args[0] + ".rupproof").exists());
        System.clearProperty("UNSATPROOF");
    }

    @Test
    public void test06DecisionModeMinOne() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-yes-ok.cnf" };
        System.setProperty("minone", "true");
        launcher.run(args);
        assertEquals(ExitCode.SATISFIABLE, launcher.getExitCode());
        System.clearProperty("minone");
    }

    @Test
    public void test07DecisionModeAllExternal() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-yes-ok.cnf" };
        System.setProperty("all", "external");
        launcher.run(args);
        assertEquals(ExitCode.SATISFIABLE, launcher.getExitCode());
        System.clearProperty("all");
    }

    @Test
    public void test08DecisionModeAllInternal() {
        BasicLauncher<ISolver> launcher = new BasicLauncher<ISolver>(
                SolverFactory.instance());
        String[] args = { "src/test/testfiles/aim-50-yes-ok.cnf" };
        System.setProperty("all", "internal");
        launcher.run(args);
        assertEquals(ExitCode.OPTIMUM_FOUND, launcher.getExitCode());
        System.clearProperty("all");
    }
}
