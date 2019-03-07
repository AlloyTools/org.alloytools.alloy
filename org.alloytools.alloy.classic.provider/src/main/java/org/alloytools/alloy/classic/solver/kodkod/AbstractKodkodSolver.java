package org.alloytools.alloy.classic.solver.kodkod;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import org.alloytools.alloy.classic.provider.AbstractCommand;
import org.alloytools.alloy.classic.provider.AlloyModuleClassic;
import org.alloytools.alloy.classic.provider.Atom;
import org.alloytools.alloy.classic.provider.TupleSet;
import org.alloytools.alloy.classic.solver.AbstractSolver;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SolverOptions;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSig;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Helper;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

public abstract class AbstractKodkodSolver extends AbstractSolver {

	public AbstractKodkodSolver(Alloy core) {
		super(core);
	}

	@Override
	public Solution solve(TCommand command, SolverOptions optionsOrNull, Instance lowerBound) {
		AbstractCommand c = (AbstractCommand) command;
		return command(command.getModule(), optionsOrNull, c.getOriginalCommand());
	}

	private Solution command(Module module, SolverOptions optionsOrNull, Command command) {

		SolverOptions options = super.processOptions(module, command, optionsOrNull);

		CompModule orig = ((AlloyModuleClassic) module).getOriginalModule();
		A4Reporter reporter = getReporter();
		A4Options opt = new A4Options();
		setOptions(opt, options);

		Map<String, Atom> atoms = new HashMap<>();

		A4Solution ai = getSolution(command, orig, reporter, opt);

		TSig univ = module.getSig("univ")
			.get();
		// TSig Int = module.getSig("Int").get();
		// TSig seqInt = module.getSig("seq/Int").get();

		return new Solution() {

			Atom createAtom(String o, TSig sig) {
				return atoms.computeIfAbsent(o, k -> {
					return new Atom(this, sig, o, o);
				});
			}

			private TupleSet to(A4TupleSet set) {
				List<IAtom> atoms = new ArrayList<>();

				for (A4Tuple tuple : set) {
					for (int j = 0; j < set.arity(); j++) {
						String atomName = tuple.atom(j);
						TSig sig = tuple.sig(j);
						//
						// A4 gives us the positive first
						// integers with type "seq/Int". Not
						// sure I understand why and it eats the
						// symbols for integers. We create a
						// special atom for the seq (not sure when
						// and where it is needed) and then create
						// the integer symbol.
						//

						if (sig.getName()
							.startsWith("seq/Int")) {
							createAtom("[" + atomName + "]", sig);
							sig = module.getSig("Int")
								.get();
						}
						Atom atom = createAtom(atomName, sig);
						atoms.add(atom);
					}
				}

				return new TupleSet(this, set.arity(), atoms);
			}

			TupleSet none = new TupleSet(this, 0, Collections.emptyList());

			@Override
			public IRelation none() {
				return none;
			}

			@Override
			public Iterator<Instance> iterator() {

				if (!isSatisfied())
					throw new IllegalStateException("This solution is not satisfied");

				return new Iterator<Instance>() {

					A4Solution nextSolution = ai;

					@Override
					public boolean hasNext() {
						return nextSolution.satisfiable();
					}

					@Override
					public Instance next() {

						if (!hasNext())
							throw new NoSuchElementException("No instance available");

						A4Solution solution = this.nextSolution;
						this.nextSolution = solution.next();

						return new Instance() {

							@Override
							public IRelation getField(TField field) {
								A4TupleSet eval = solution.eval((Field) field);

								return to(eval);
							}

							@Override
							public IRelation getAtoms(TSig sig) {
								A4TupleSet set = solution.eval((Sig) sig);

								return to(set);
							}

							@Override
							public IRelation getVariable(String fun, String var) {
								String name = "$" + command.getName() + "_" + var;
								for (ExprVar skolem : solution.getAllSkolems()) {
									if (skolem.label.equals(name)) {
										A4TupleSet set = (A4TupleSet) solution.eval(skolem);
										return to(set);
									}
								}
								return null;
							}

							@Override
							public IRelation eval(String cmd) {
								// TODO Auto-generated method stub
								return null;
							}

							@Override
							public TupleSet universe() {
								A4TupleSet eval = ai.eval((Sig) univ);
								return to(eval);
							}

							@Override
							public IRelation ident() {
								return universe().toIdent();
							}

						};
					}
				};
			}

			@Override
			public boolean isSatisfied() {
				return ai.satisfiable();
			}

			@Override
			public Solver getSolver() {
				return AbstractKodkodSolver.this;
			}

			@Override
			public Module getModule() {
				return module;
			}

			@Override
			public TCommand getCommand() {
				return command;
			}

			@Override
			public SolverOptions getOptions() {
				return options;
			}

		};
	}

	protected A4Solution getSolution(Command command, CompModule orig, A4Reporter reporter, A4Options opt) {
		return TranslateAlloyToKodkod.execute_command(reporter, orig.getAllReachableSigs(), command, opt);
	}

	public static SatSolver toSatSolver(String id) {

		Map<String, SatSolver> solvers = getClassicKodkodSolvers();
		SatSolver satSolver = solvers.get(id);
		return satSolver;
	}

	public static Map<String, SatSolver> getClassicKodkodSolvers() {
		Map<String, SatSolver> classicSolvers = new HashMap<>();
		for (SatSolver satSolver : SatSolver.values()) {
			classicSolvers.put(satSolver.id(), satSolver);
		}
		return classicSolvers;
	}

	public boolean isAvailable() {
		return SATFactory.available(getSATFactory());
	}

	/**
	 * Moves the modern options to the classic options. In the default case we
	 * setup a helper callback that allows us to set the options on the Kodkod
	 * solver.
	 * 
	 * @param classic the classic options
	 * @param modern the modern options
	 */
	protected void setOptions(A4Options classic, SolverOptions modern) {
		classic.a4Helper = new A4Helper() {

			@Override
			public void setupSolver(A4Solution solution) {
				setup((KodkodOptions) modern, solution);
			}
		};
	}

	/**
	 * @param options
	 * @param solution
	 */
	protected void setup(KodkodOptions options, A4Solution solution) {

		kodkod.engine.Solver solver = solution.getSolver();
		solver.options()
			.setSymmetryBreaking(options.symmetry);
		solver.options()
			.setSkolemDepth(options.skolemDepth);
		solver.options()
			.setNoOverflow(options.noOverflow);
		solver.options()
			.setSolver(getSATFactory(options));
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

}
