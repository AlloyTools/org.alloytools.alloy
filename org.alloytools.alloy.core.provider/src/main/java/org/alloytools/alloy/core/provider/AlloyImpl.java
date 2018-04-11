package org.alloytools.alloy.core.provider;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.alloytools.alloy.control.api.Alloy;
import org.alloytools.alloy.core.api.AlloyCompiler;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.SourceResolver;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.AlloyOptions;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.AlloySolver;
import org.alloytools.alloy.solver.api.IAtom;
import org.alloytools.alloy.solver.api.ITupleSet;
import org.alloytools.alloy.solver.api.SolverType;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class AlloyImpl implements Alloy {

    interface AlloyModuleImpl extends AlloyModule {

        CompModule getOriginalModule();
    }

    @Override
    public List<AlloySolver> getSolvers() {
        return null;
    }

    @Override
    public AlloySolver getDefaultSolver() {
        return new AlloySolver() {


            @Override
            public SolverType getSolverType() {
                return SolverType.OTHER;
            }

            @Override
            public String getName() {
                return "kodkod";
            }

            @Override
            public String getDescription() {
                return "Kodkod with SAT4J";
            }

            @Override
            public AlloySolution run(AlloyModule module, TRun run) {
                A4Reporter reporter = new A4Reporter();
                A4Options opt = new A4Options();
                CompModule orig = ((AlloyModuleImpl) module).getOriginalModule();

                Command command = (Command) run;
                Map<String,Atom> atoms = new HashMap<>();
                opt.noOverflow=true;
                A4Solution ai = TranslateAlloyToKodkod.execute_command(reporter, orig.getAllReachableSigs(), command, opt);
             
                TSig univ = module.getSig("univ").get();
                TSig Int = module.getSig("Int").get();
                TSig seqInt = module.getSig("seq/Int").get();

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
                                        String name = "$" + run.getName() + "_" + var;
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

            @Override
            public AlloySolution check(AlloyModule module, TCheck command) {
                // TODO Auto-generated method stub
                return null;
            }

			@Override
			public AlloyOptions getOptions() {
				// TODO Auto-generated method stub
				return null;
			}

			@Override
			public void setOptions() {
				// TODO Auto-generated method stub
				
			}


        };
    }



    @Override
    public AlloyCompiler compiler(SourceResolver resolver) {
        return new AlloyCompiler() {

            @Override
            public AlloyModule compile(File file) throws Exception {
                return compileSource(new String(Files.readAllBytes(file.toPath()), "UTF-8"));
            }

            @Override
            public AlloyModule compileSource(String source) throws Exception {
                A4Reporter reporter = new A4Reporter();
                CompModule module = CompUtil.parseEverything_fromString(reporter, source);
                return new AlloyModuleImpl() {

                    @Override
                    public List<TSig> getSigs() {
                        ConstList<Sig> sigs = module.getAllReachableSigs();

                        return new ArrayList<>(sigs);
                    }

                    @Override
                    public Optional< ? extends TSig> getSig(String name) {
                        return getSigs().stream().filter(s -> s.getName().equals(name)).findAny();
                    }

                    @Override
                    public List<TRun> getRuns() {
                        return module.getAllCommands().stream().filter(c -> !c.isCheck()).collect(Collectors.toList());
                    }

                    @Override
                    public List<TCheck> getChecks() {
                        return module.getAllCommands().stream().filter(c -> c.isCheck()).collect(Collectors.toList());
                    }

                    @Override
                    public CompModule getOriginalModule() {
                        return module;
                    }

                };
            }
        };
    }

    @Override
    public AlloyCompiler compiler() {
        return compiler(new SourceResolver() {

            @Override
            public String resolve(String path) throws IOException {
                File file = new File(path);
                return new String(Files.readAllBytes(file.toPath()), "UTF-8");
            }
        });
    }

}
