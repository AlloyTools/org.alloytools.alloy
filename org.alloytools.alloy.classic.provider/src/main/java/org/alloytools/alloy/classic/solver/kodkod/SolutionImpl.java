package org.alloytools.alloy.classic.solver.kodkod;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;

import org.alloytools.alloy.classic.provider.Atom;
import org.alloytools.alloy.classic.provider.Relation;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.api.SolverOptions;
import org.alloytools.alloy.core.api.TCommand;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.A4Solution;

class SolutionImpl implements Solution {

    final Map<String,Atom> atoms  = new HashMap<>();
    final Relation         none   = new Relation(this, false);
    final Relation         truthy = new Relation(this, true);
    final Module           module;
    final Command          command;
    final A4Solution       initial;
    final Solver           solver;
    final SolverOptions    options;


    public SolutionImpl(Module module, Solver solver, A4Solution initial, Command command, SolverOptions options) {
        this.module = module;
        this.solver = solver;
        this.initial = initial;
        this.command = command;
        this.options = options;
    }

    @Override
    public IRelation none() {
        return none;
    }

    @Override
    public Iterator<Instance> iterator() {
        if (!isSatisfied())
            throw new IllegalStateException("This solution is not satisfied");


        return new Iterator<Instance>() {

            boolean    used    = false;
            A4Solution current = initial;

            @Override
            public boolean hasNext() {
                if (!current.satisfiable())
                    return false;

                if (used) {
                    current = fork(current, hasVariables() ? -1 : -3);
                    used = false;
                }
                return current.satisfiable();
            }

            @Override
            public Instance next() {
                if (!hasNext())
                    throw new NoSuchElementException("No instance available");

                used = true;

                return new InstanceImpl(SolutionImpl.this, current, -1);
            }
        };
    }

    @Override
    public boolean isSatisfied() {
        return initial.satisfiable();
    }

    @Override
    public Solver getSolver() {
        return solver;
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

    @Override
    public boolean hasVariables() {
        // TODO sigs can also be variable
        return getModule().getSignatures().values().stream().flatMap(sig -> sig.getFieldMap().values().stream()).filter(field -> field.isVariable()).findAny().isPresent();
    }

    @Override
    public String toString() {
        return "Solution[" + module + "," + solver + "," + command + "]";
    }

    @Override
    public Iterable<Trace> trace(Instance seed) {
        InstanceImpl impl = (InstanceImpl) seed;
        if (impl.solution != this)
            throw new RuntimeException("The current instance " + seed + " is not from the right solution");

        if (!hasVariables())
            throw new RuntimeException("This module has no variables");

        return () -> new Iterator<Trace>() {

            boolean    used    = false;
            A4Solution current = impl.ai;

            @Override
            public boolean hasNext() {

                if (!current.satisfiable())
                    return false;

                if (used) {
                    if (impl.state < 0) {
                        current = fork(current, -3);
                    } else {
                        current = fork(current, impl.state);
                    }
                    used = false;
                }
                return current.satisfiable();
            }

            @Override
            public Trace next() {
                if (!hasNext())
                    throw new NoSuchElementException("No more instances");

                used = true;

                int length = current.getTraceLength();
                int loop = current.getLoopState();
                InstanceImpl[] instances = new InstanceImpl[length];
                for (int i = 0; i < instances.length; i++) {
                    instances[i] = new InstanceImpl(impl.solution, current, i);
                }

                return new Trace() {

                    @Override
                    public Instance[] instances() {
                        return instances;
                    }

                    @Override
                    public int loop() {
                        return loop;
                    }
                };
            }
        };
    }


    A4Solution fork(A4Solution solution, int state) {
        return solution.fork(state);
    }

    public IRelation truthy() {
        return truthy;
    }
}
