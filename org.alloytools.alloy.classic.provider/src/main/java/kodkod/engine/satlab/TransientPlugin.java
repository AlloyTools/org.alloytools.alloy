package kodkod.engine.satlab;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;

public class TransientPlugin extends AbstractKodkodSolver {

    final SATSolver solver;

    public TransientPlugin(Alloy core, SATSolver solver) {
        super(core);
        this.solver = solver;
    }

    @Override
    public String getId() {
        return ".transient";
    }

    @Override
    public String getName() {
        return "private transient plugin";
    }

    @Override
    public SolverType getSolverType() {
        return SolverType.PRIVATE;
    }

    @Override
    public String getDescription() {
        return "can be used to inject a classic solver";
    }

    @Override
    public SATFactory getSATFactory(KodkodOptions options) {
        return new SATFactory() {

            @Override
            public SATSolver instance() {
                return solver;
            }

            @Override
            public String toString() {
                return getId();
            }
        };
    }
}
