package kodkod.solvers;

import java.util.Optional;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class PMaxSAT4JRef extends SATFactory {
	private static final long		serialVersionUID	= 1L;
	public static SATFactory INSTANCE = new PMaxSAT4JRef();
	
	private PMaxSAT4JRef() {}
	
	@Override
	public String id() {
		return "sat4j.pmax";
	}

	public boolean maxsat() {
		return true;
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
	public SATSolver instance() {
		return new PMaxSAT4J(
				org.sat4j.maxsat.SolverFactory.newDefault());
	}
	@Override
	public String type() {
		return "java";
	}

}
