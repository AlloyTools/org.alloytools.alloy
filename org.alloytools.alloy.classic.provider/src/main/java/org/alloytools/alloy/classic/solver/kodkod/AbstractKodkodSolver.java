package org.alloytools.alloy.classic.solver.kodkod;

import java.util.HashMap;
import java.util.Map;

import org.allotools.conversion.util.DTOs;
import org.alloytools.alloy.classic.provider.AbstractCommand;
import org.alloytools.alloy.classic.provider.AlloyModuleClassic;
import org.alloytools.alloy.classic.solver.AbstractSolver;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.SolverOptions;
import org.alloytools.alloy.core.api.TCommand;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

public abstract class AbstractKodkodSolver extends AbstractSolver {

    public AbstractKodkodSolver(Alloy core) {
        super(core);
    }

    @Override
    public Solution solve(TCommand command, SolverOptions optionsOrNull, Instance lowerBound, Instance upperBound) {
        AbstractCommand c = (AbstractCommand) command;
        return command(command.getModule(), optionsOrNull, c.getOriginalCommand());
    }

    private Solution command(Module module, SolverOptions optionsOrNull, Command command) {
        SolverOptions options = super.processOptions(module, command, optionsOrNull);

        A4Reporter reporter = getReporter();
        A4Options opt = new A4Options();
        CompModule orig = ((AlloyModuleClassic) module).getOriginalModule();
        A4Solution solution = getSolution(command, orig, reporter, opt, options);

        return new SolutionImpl(module, this, solution, command, options);
    }

    protected A4Solution getSolution(Command command, CompModule orig, A4Reporter reporter, A4Options opt, SolverOptions options) {
        opt.fixupPardinusOptions = eo -> {
            DTOs.copyDTOToBean(options, eo);
        };
        return TranslateAlloyToKodkod.execute_command(reporter, orig.getAllReachableSigs(), command, opt);
    }

    public static SatSolver toSatSolver(String id) {

        Map<String,SatSolver> solvers = getClassicKodkodSolvers();
        SatSolver satSolver = solvers.get(id);
        return satSolver;
    }

    public static Map<String,SatSolver> getClassicKodkodSolvers() {
        Map<String,SatSolver> classicSolvers = new HashMap<>();
        for (SatSolver satSolver : SatSolver.values()) {
            classicSolvers.put(satSolver.id(), satSolver);
        }
        return classicSolvers;
    }

    @Override
    public boolean isAvailable() {
        return SATFactory.available(getSATFactory());
    }

    protected abstract SATFactory getSATFactory(KodkodOptions options);

    protected SATFactory getSATFactory() {
        try {
            KodkodOptions options = (KodkodOptions) newOptions();
            return getSATFactory(options);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    protected A4Reporter getReporter() {
        return new A4Reporter();
    }

    @Override
    public SolverOptions newOptions() {
        return new KodkodOptions();
    }

    public boolean isUnbounded() {
        return false;
    }

    public boolean isIncremental() {
        return true;
    }

    @Override
    public String toString() {
        return "AbstractKodkodSolver []";
    }

    @Override
    public boolean isJavaOnly() {
        return false;
    }
}
