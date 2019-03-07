package org.alloytools.alloy.solver.plingeling.natve;

import java.util.ArrayList;
import java.util.List;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.alloytools.nativecode.util.NativeCode;

import kodkod.engine.satlab.SATFactory;

public class PlingelingPlugin extends AbstractKodkodSolver {


    public static class PlingelingOptions extends KodkodOptions {

        public int     threads   = 1;
        public boolean portfolio = false;
    }

    public PlingelingPlugin(Alloy core) {
        super(core);
    }

    @Override
    public String getId() {
        return "plingeling(jni)";
    }

    @Override
    public SolverType getSolverType() {
        return SolverType.SAT;
    }

    @Override
    public String getName() {
        return "Plingeling";
    }

    @Override
    public String getDescription() {
        return "Plingeling";
    }

    @Override
    public PlingelingOptions newOptions() {
        return new PlingelingOptions();
    }

    @Override
    protected SATFactory getSATFactory(KodkodOptions options) {
        PlingelingOptions poptions = (PlingelingOptions) options;

        final List<String> opts = new ArrayList<String>(3);
        if (poptions.threads > 1)
            opts.add("-t");

        opts.add(Integer.toString(poptions.threads));

        if (poptions.portfolio)
            opts.add("-p");

        final String executable = NativeCode.cacheBinary(getAlloy().getPreferencesDir("binary").toPath(), "plingeling").toFile().getAbsolutePath();
        return SATFactory.externalFactory(executable == null ? "plingeling" : executable, null, opts.toArray(new String[opts.size()]));
    }

}
