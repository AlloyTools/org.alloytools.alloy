package org.alloytools.nativecode.util;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertNotNull;

import org.alloytools.alloy.classic.provider.AlloyClassicFacade;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.nativecode.v1.util.NativeCode;
import org.alloytools.nativecode.v1.util.NativeCode.Platform;
import org.junit.Test;

import kodkod.engine.satlab.GlucosePlugin;
import kodkod.engine.satlab.SATSolver;

public class NativeCodeTest {

    @Test
    public void testNative() {
        Platform platform = NativeCode.platform;
        assertNotNull(platform);
        System.out.println(platform);
    }



    @Test
    public void testGlucose() {
        GlucosePlugin glucosePlugin = new GlucosePlugin(new AlloyClassicFacade());
        SATSolver solver = glucosePlugin.getSATFactory(new KodkodOptions()).instance();
        assertThat(solver).isNotNull();
        boolean solve = solver.solve();
    }


    @Test
    public void testMinisat() {
        AlloyClassicFacade alloy = new AlloyClassicFacade();
        System.out.println(alloy.getSolvers().keySet());
        Solver minisat = alloy.getSolvers().get("minisat");
        assertThat(minisat).isNotNull();
        TModule m = alloy.compiler().compileSource("sig Foo {} run { some Foo }");
        TCommand c = m.getDefaultCommand();
        Solution solve = minisat.solve(c, null);
        assertThat(solve.isSatisfied()).isTrue();
    }

    @Test
    public void testPlingeling() {
        AlloyClassicFacade alloy = new AlloyClassicFacade();
        System.out.println(alloy.getSolvers().keySet());
        Solver plingeling = alloy.getSolvers().get("plingeling");
        assertThat(plingeling).isNotNull();
        TModule m = alloy.compiler().compileSource("sig Foo {} run { some Foo }");
        TCommand c = m.getDefaultCommand();
        Solution solve = plingeling.solve(c, null);
        assertThat(solve.isSatisfied()).isTrue();
    }
}
