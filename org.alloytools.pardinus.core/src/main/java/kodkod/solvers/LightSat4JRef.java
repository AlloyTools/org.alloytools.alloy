package kodkod.solvers;

import java.util.Optional;

import org.sat4j.minisat.SolverFactory;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class LightSat4JRef extends SATFactory {
	private static final long serialVersionUID = 1L;
	public static final SATFactory INSTANCE = new LightSat4JRef();

	private LightSat4JRef() {}
	
	@Override
	public String id() {
		return "sat4j.light";
	}

	public SATSolver instance() {
		return new SAT4J(SolverFactory.instance().lightSolver());
	}

	@Override
	public boolean incremental() {
		return true;
	}
	@Override
	public Optional<String> getDescription() {
		return Optional.of("SAT4J is a Java library used for solving Boolean Satisfiability (SAT) problems and more generally Pseudo-Boolean (PB) problems. It is an open-source project under the GNU LGPL license, providing various SAT and MaxSAT solvers in Java. It is very reliable and works on all platforms");
	}

	@Override
	public String type() {
		return "java";
	}
	
}
