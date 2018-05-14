package org.alloytools.alloy.classic.solver.kodkod;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.alloytools.alloy.classic.provider.AlloyModuleClassic;
import org.alloytools.alloy.classic.provider.Atom;
import org.alloytools.alloy.classic.provider.TupleSet;
import org.alloytools.alloy.classic.solver.AbstractSolver;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.AlloyOptions;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.IAtom;
import org.alloytools.alloy.solver.api.ITupleSet;

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
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;

public abstract class AbstractKodkodSolver extends AbstractSolver {

    public AbstractKodkodSolver(Alloy core) {
        super(core);
    }

    @Override
    public AlloySolution run(AlloyModule module, AlloyOptions optionsOrNull, TRun run) {

        Command command = (Command) run;
        
        return command(module, optionsOrNull, command);
    }

	private AlloySolution command(AlloyModule module, AlloyOptions optionsOrNull, Command command) {
		
		AlloyOptions options = super.processOptions(module, command, optionsOrNull);
		
        CompModule orig = ((AlloyModuleClassic) module).getOriginalModule();
        A4Reporter reporter = getReporter();
        A4Options opt = new A4Options();
        setOptions(opt, options);
        
        Map<String,Atom> atoms = new HashMap<>();

        A4Solution ai = getSolution(command, orig, reporter, opt);

        TSig univ = module.getSig("univ").get();
        // TSig Int = module.getSig("Int").get();
        // TSig seqInt = module.getSig("seq/Int").get();

        return new AlloySolution() {

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

                        if (sig.getName().startsWith("seq/Int")) {
                            createAtom("[" + atomName + "]", sig);
                            sig = module.getSig("Int").get();
                        }
                        Atom atom = createAtom(atomName, sig);
                        atoms.add(atom);
                    }
                }

                return new TupleSet(this, set.arity(), atoms);
            }

            TupleSet none = new TupleSet(this, 0, Collections.emptyList());

            @Override
            public ITupleSet none() {
                return none;
            }

            @Override
            public Iterator<AlloyInstance> iterator() {
                return new Iterator<AlloyInstance>() {

                    A4Solution solution = ai;
                    boolean    first    = true;

                    @Override
                    public boolean hasNext() {
                        if (!first) {
                            solution = solution.next();
                        }
                        return solution.satisfiable();
                    }

                    @Override
                    public AlloyInstance next() {
                        first = false;
                        return new AlloyInstance() {

                            @Override
                            public ITupleSet getField(TField field) {
                                A4TupleSet eval = solution.eval((Field) field);

                                return to(eval);
                            }

                            @Override
                            public ITupleSet getAtoms(TSig sig) {
                                A4TupleSet set = solution.eval((Sig) sig);

                                return to(set);
                            }

                            @Override
                            public ITupleSet getVariable(String fun, String var) {
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
                            public ITupleSet eval(String cmd) {
                                // TODO Auto-generated method stub
                                return null;
                            }

                            @Override
                            public TupleSet universe() {
                                A4TupleSet eval = ai.eval((Sig) univ);
                                return to(eval);
                            }

                            @Override
                            public ITupleSet ident() {
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
        };
	}


	protected A4Solution getSolution(Command command, CompModule orig, A4Reporter reporter, A4Options opt) {
		return TranslateAlloyToKodkod.execute_command(reporter, orig.getAllReachableSigs(), command, opt);
	}

    @Override
    public AlloySolution check(AlloyModule module, AlloyOptions options, TCheck command) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException();
    }

    @Override
    public Class< ? extends AlloyOptions> getOptionsType() {
        return KodkodOptions.class;
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

    public boolean isAvailable() {
        return SATFactory.available(getSATFactory());
    }

	/**
	 * Moves the modern options to the classic options. In the default
	 * case we setup a helper callback that allows us to set the options
	 * on the Kodkod solver.
	 * 
	 * @param classic the classic options
	 * @param modern the modern options
	 */
	protected void setOptions(A4Options classic, AlloyOptions modern) {
		classic.a4Helper = new A4Helper() {
			
			@Override
			public void setupSolver(A4Solution solution) {
				setup((KodkodOptions) modern, solution);
			}
		};
	}

	/**
	 * 
	 * @param options
	 * @param solution
	 */
	protected void setup(KodkodOptions options, A4Solution solution) {
		
        Solver solver = solution.getSolver();
        solver.options().setSymmetryBreaking(options.symmetry);
        solver.options().setSkolemDepth(options.skolemDepth);
        solver.options().setNoOverflow(options.noOverflow);
        solver.options().setSolver( getSATFactory(options));
    }

    protected abstract SATFactory getSATFactory(KodkodOptions options);

    protected SATFactory getSATFactory() {
        try {
            KodkodOptions options = (KodkodOptions)getOptionsType().newInstance();
            return getSATFactory(options);
        } catch( Exception e) {
            throw new RuntimeException(e);
        }
    }

	protected A4Reporter getReporter() {
		return new A4Reporter();
	}


}
