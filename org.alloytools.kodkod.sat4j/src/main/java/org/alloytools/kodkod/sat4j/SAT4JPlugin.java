package org.alloytools.kodkod.sat4j;

import org.alloytools.alloy.classic.solver.kodkod.AbstractKodkodSolver;
import org.alloytools.alloy.classic.solver.kodkod.KodkodOptions;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.SolverType;
import org.sat4j.minisat.SolverFactory;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class SAT4JPlugin extends AbstractKodkodSolver {

	public SAT4JPlugin(Alloy core) {
		super(core);
	}

	@Override
	public String getId() {
		return "sat4j";
	}

	@Override
	public SolverType getSolverType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getName() {
		return "SAT4J";
	}

	@Override
	public String getDescription() {
		return "Sat4j is a full featured boolean reasoning library designed to bring state-of-the-art SAT technologies to the Java Virtual Machine.";
	}

	@Override
	protected SATFactory getSATFactory(KodkodOptions options) {
		return new SATFactory() {

            @Override
            public SATSolver instance() {
                return new SAT4J(SolverFactory.instance().defaultSolver());
            }

            @Override
            public String toString() {
                return "DefaultSAT4J";
            }
        };
	}

}
