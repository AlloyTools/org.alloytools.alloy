/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2013 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.tools;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import org.sat4j.annotations.Feature;
import org.sat4j.core.ASolverFactory;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Counter;
import org.sat4j.specs.AssignmentOrigin;
import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.specs.UnitClauseConsumer;
import org.sat4j.specs.UnitClauseProvider;
import org.sat4j.specs.UnitPropagationListener;

/**
 * A class allowing to run several solvers in parallel.
 * 
 * Note that each solver will have its own copy of the CNF, so it is not a
 * memory efficient implementation. There is no sharing of information yet
 * between the solvers.
 * 
 * @author leberre
 * 
 * @param <S>
 *            the type of the solver (ISolver of IPBSolver)
 */
@Feature("solver")
public class ManyCore<S extends ISolver> implements ISolver, OutcomeListener,
        UnitClauseProvider, UnitClauseConsumer {

    private static final int NORMAL_SLEEP = 500;

    private static final int FAST_SLEEP = 50;

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final String[] availableSolvers; // = { };

    protected final List<S> solvers;
    protected final int numberOfSolvers;
    private int winnerId = -1;
    private boolean resultFound;
    private AtomicInteger remainingSolvers;
    private volatile int sleepTime;
    private volatile boolean solved;
    private final IVecInt sharedUnitClauses = new VecInt();

    private final IVec<Counter> solversStats = new Vec<Counter>();

    public ManyCore(ASolverFactory<S> factory, String... solverNames) {
        this(factory, false, solverNames);
    }

    public ManyCore(ASolverFactory<S> factory, boolean shareLearnedUnitClauses,
            String... solverNames) {
        this.availableSolvers = solverNames;
        this.numberOfSolvers = solverNames.length;
        this.solvers = new ArrayList<S>(this.numberOfSolvers);
        S solver;
        for (int i = 0; i < this.numberOfSolvers; i++) {
            solver = factory.createSolverByName(this.availableSolvers[i]);
            solver.setUnitClauseConsumer(this);
            if (shareLearnedUnitClauses) {
                solver.setUnitClauseProvider(this);
            }
            this.solvers.add(solver);
            this.solversStats.push(new Counter(0));
        }
    }

    /**
     * Create a parallel solver from a list of solvers and a list of names.
     * 
     * @param names
     *            a String to describe each solver in the messages.
     * @param solverObjects
     *            the solvers
     */
    public ManyCore(String[] names, S... solverObjects) {
        this(false, names, solverObjects);
    }

    public ManyCore(boolean shareLearnedUnitClauses, String[] names,
            S... solverObjects) {
        this(shareLearnedUnitClauses, solverObjects);
        for (int i = 0; i < names.length; i++) {
            this.availableSolvers[i] = names[i];
        }
    }

    public ManyCore(S... solverObjects) {
        this(false, solverObjects);
    }

    public ManyCore(boolean shareLearnedUnitClauses, S... solverObjects) {
        this.availableSolvers = new String[solverObjects.length];
        for (int i = 0; i < solverObjects.length; i++) {
            this.availableSolvers[i] = "solver" + i;
        }
        this.numberOfSolvers = solverObjects.length;
        this.solvers = new ArrayList<S>(this.numberOfSolvers);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.add(solverObjects[i]);
            solverObjects[i].setUnitClauseConsumer(this);
            if (shareLearnedUnitClauses) {
                solverObjects[i].setUnitClauseProvider(this);
            }
            this.solversStats.push(new Counter(0));
        }
    }

    public void addAllClauses(IVec<IVecInt> clauses)
            throws ContradictionException {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).addAllClauses(clauses);
        }
    }

    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addAtLeast(literals, degree));
        }
        return group;
    }

    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addAtMost(literals, degree));
        }
        return group;
    }

    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addExactly(literals, n));
        }
        return group;
    }

    public IConstr addClause(IVecInt literals) throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addClause(literals));
        }
        return group;
    }

    public void clearLearntClauses() {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).clearLearntClauses();
        }
        sharedUnitClauses.clear();
    }

    public void expireTimeout() {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).expireTimeout();
        }
        this.sleepTime = FAST_SLEEP;
    }

    public Map<String, Number> getStat() {
        return this.solvers.get(this.getWinnerId()).getStat();
    }

    public int getTimeout() {
        return this.solvers.get(0).getTimeout();
    }

    public long getTimeoutMs() {
        return this.solvers.get(0).getTimeoutMs();
    }

    public int newVar() {
        throw new UnsupportedOperationException();
    }

    public int newVar(int howmany) {
        int result = 0;
        for (int i = 0; i < this.numberOfSolvers; i++) {
            result = this.solvers.get(i).newVar(howmany);
        }
        return result;
    }

    @Deprecated
    public void printStat(PrintStream out, String prefix) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            out.printf(
                    "%s>>>>>>>>>> Solver number %d (%d answers) <<<<<<<<<<<<<<<<<<%n",
                    prefix, i, this.solversStats.get(i).getValue());
            this.solvers.get(i).printStat(out, prefix);
        }
    }

    @Deprecated
    public void printStat(PrintWriter out, String prefix) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            out.printf(
                    "%s>>>>>>>>>> Solver number %d (%d answers) <<<<<<<<<<<<<<<<<<%n",
                    prefix, i, this.solversStats.get(i).getValue());
            this.solvers.get(i).printStat(out, prefix);
        }
    }

    public boolean removeConstr(IConstr c) {
        if (c instanceof ConstrGroup) {
            ConstrGroup group = (ConstrGroup) c;
            boolean removed = true;
            IConstr toRemove;
            for (int i = 0; i < this.numberOfSolvers; i++) {
                toRemove = group.getConstr(i);
                if (toRemove != null) {
                    removed = removed
                            & this.solvers.get(i).removeConstr(toRemove);
                }
            }
            sharedUnitClauses.clear();
            return removed;
        }
        throw new IllegalArgumentException(
                "Can only remove a group of constraints!");
    }

    public void reset() {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).reset();
        }
        sharedUnitClauses.clear();
    }

    public void setExpectedNumberOfClauses(int nb) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setExpectedNumberOfClauses(nb);
        }
    }

    public void setTimeout(int t) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setTimeout(t);
        }
    }

    public void setTimeoutMs(long t) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setTimeoutMs(t);
        }
    }

    public void setTimeoutOnConflicts(int count) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setTimeoutOnConflicts(count);
        }
    }

    public String toString(String prefix) {
        StringBuilder res = new StringBuilder();
        res.append(prefix);
        res.append("ManyCore solver with ");
        res.append(this.numberOfSolvers);
        res.append(" solvers running in parallel");
        res.append("\n");
        for (int i = 0; i < this.numberOfSolvers; i++) {
            res.append(prefix);
            res.append(">>>>>>>>>> Solver number ");
            res.append(i);
            res.append(" <<<<<<<<<<<<<<<<<<\n");
            res.append(this.solvers.get(i).toString(prefix));
            if (i < this.numberOfSolvers - 1) {
                res.append("\n");
            }
        }
        return res.toString();
    }

    public int[] findModel() throws TimeoutException {
        if (isSatisfiable()) {
            return model();
        }
        // A zero length array would mean that the formula is a tautology.
        return null;
    }

    public int[] findModel(IVecInt assumps) throws TimeoutException {
        if (isSatisfiable(assumps)) {
            return model();
        }
        // A zero length array would mean that the formula is a tautology.
        return null;
    }

    public boolean isSatisfiable() throws TimeoutException {
        return isSatisfiable(VecInt.EMPTY, false);
    }

    public synchronized boolean isSatisfiable(IVecInt assumps,
            boolean globalTimeout) throws TimeoutException {
        this.remainingSolvers = new AtomicInteger(this.numberOfSolvers);
        this.solved = false;
        for (int i = 0; i < this.numberOfSolvers; i++) {
            new Thread(new RunnableSolver(i, this.solvers.get(i), assumps,
                    globalTimeout, this)).start();
        }
        try {
            this.sleepTime = NORMAL_SLEEP;
            do {
                wait(this.sleepTime);
            } while (this.remainingSolvers.get() > 0);
        } catch (InterruptedException e) {
            // will happen when one solver found a solution
            Thread.currentThread().interrupt();
        }
        if (!this.solved) {
            assert this.remainingSolvers.get() == 0;
            throw new TimeoutException();
        }
        return this.resultFound;
    }

    public boolean isSatisfiable(boolean globalTimeout)
            throws TimeoutException {
        return isSatisfiable(VecInt.EMPTY, globalTimeout);
    }

    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        return isSatisfiable(assumps, false);
    }

    public int[] model() {
        return this.solvers.get(this.getWinnerId()).model();
    }

    public boolean model(int var) {
        return this.solvers.get(this.getWinnerId()).model(var);
    }

    public int nConstraints() {
        return this.solvers.get(0).nConstraints();
    }

    public int nVars() {
        return this.solvers.get(0).nVars();
    }

    public void printInfos(PrintWriter out, String prefix) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            out.printf("%s>>>>>>>>>> Solver number %d <<<<<<<<<<<<<<<<<<%n",
                    prefix, i);
            this.solvers.get(i).printInfos(out, prefix);
        }
    }

    public synchronized void onFinishWithAnswer(boolean finished,
            boolean result, int index) {
        if (finished && !this.solved) {
            this.winnerId = index;
            this.solversStats.get(index).inc();
            this.solved = true;
            this.resultFound = result;
            for (int i = 0; i < this.numberOfSolvers; i++) {
                if (i != this.getWinnerId()) {
                    this.solvers.get(i).expireTimeout();
                }
            }
            this.sleepTime = FAST_SLEEP;
            if (isVerbose()) {
                System.out.println(getLogPrefix() + "And the winner is "
                        + this.availableSolvers[this.getWinnerId()]);
            }
        }
        this.remainingSolvers.getAndDecrement();
    }

    public boolean isDBSimplificationAllowed() {
        return this.solvers.get(0).isDBSimplificationAllowed();
    }

    public void setDBSimplificationAllowed(boolean status) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setDBSimplificationAllowed(status);
        }
    }

    public <I extends ISolverService> void setSearchListener(
            SearchListener<I> sl) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setSearchListener(sl);
        }
    }

    /**
     * @since 2.2
     */
    public <I extends ISolverService> SearchListener<I> getSearchListener() {
        return this.solvers.get(0).getSearchListener();
    }

    public int nextFreeVarId(boolean reserve) {
        int res = -1;
        for (int i = 0; i < this.numberOfSolvers; ++i) {
            res = this.solvers.get(i).nextFreeVarId(reserve);
        }
        return res;
    }

    public IConstr addBlockingClause(IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addBlockingClause(literals));
        }
        return group;
    }

    private void checkWinnerId() {
        if (this.winnerId < 0) {
            throw new IllegalStateException("No solver solved the problem!");
        }
    }

    public IVecInt createBlockingClauseForCurrentModel() {
        return this.solvers.get(this.getWinnerId())
                .createBlockingClauseForCurrentModel();
    }

    public IConstr discardCurrentModel() throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        IVecInt blockingClause = createBlockingClauseForCurrentModel();
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addBlockingClause(blockingClause));
        }
        return group;
    }

    public boolean removeSubsumedConstr(IConstr c) {
        if (c instanceof ConstrGroup) {
            ConstrGroup group = (ConstrGroup) c;
            boolean removed = true;
            IConstr toRemove;
            for (int i = 0; i < this.numberOfSolvers; i++) {
                toRemove = group.getConstr(i);
                if (toRemove != null) {
                    removed = removed & this.solvers.get(i)
                            .removeSubsumedConstr(toRemove);
                }
            }
            return removed;
        }
        throw new IllegalArgumentException(
                "Can only remove a group of constraints!");
    }

    public boolean isVerbose() {
        return this.solvers.get(0).isVerbose();
    }

    public void setVerbose(boolean value) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setVerbose(value);
        }
    }

    public void setLogPrefix(String prefix) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setLogPrefix(prefix);
        }

    }

    public String getLogPrefix() {
        return this.solvers.get(0).getLogPrefix();
    }

    public IVecInt unsatExplanation() {
        return this.solvers.get(this.getWinnerId()).unsatExplanation();
    }

    public int[] primeImplicant() {
        return this.solvers.get(this.getWinnerId()).primeImplicant();
    }

    /**
     * @since 2.3.2
     */
    public boolean primeImplicant(int p) {
        return this.solvers.get(this.getWinnerId()).primeImplicant(p);
    }

    public List<S> getSolvers() {
        return new ArrayList<S>(this.solvers);
    }

    public int[] modelWithInternalVariables() {
        return this.solvers.get(this.getWinnerId())
                .modelWithInternalVariables();
    }

    public int realNumberOfVariables() {
        return this.solvers.get(0).realNumberOfVariables();
    }

    public void registerLiteral(int p) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).registerLiteral(p);
        }

    }

    public boolean isSolverKeptHot() {
        return this.solvers.get(0).isSolverKeptHot();
    }

    public void setKeepSolverHot(boolean value) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            this.solvers.get(i).setKeepSolverHot(value);
        }

    }

    public ISolver getSolvingEngine() {
        throw new UnsupportedOperationException(
                "Not supported yet in ManyCore");
    }

    /**
     * @since 2.3.3
     */
    public void printStat(PrintWriter out) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            out.printf(
                    "%s>>>>>>>>>> Solver number %d (%d answers) <<<<<<<<<<<<<<<<<<%n",
                    this.solvers.get(i).getLogPrefix(), i,
                    this.solversStats.get(i).getValue());
            this.solvers.get(i).printStat(out);
        }
    }

    /**
     * @since 2.3.3
     */
    public void printInfos(PrintWriter out) {
        for (int i = 0; i < this.numberOfSolvers; i++) {
            out.printf("%s>>>>>>>>>> Solver number %d <<<<<<<<<<<<<<<<<<%n",
                    getLogPrefix(), i);
            this.solvers.get(i).printInfos(out);
        }

    }

    @Override
    public synchronized void learnUnit(int p) {
        sharedUnitClauses.push(LiteralsUtils.toInternal(p));
    }

    @Override
    @Feature(value = "unitclauseprovider", parent = "expert")
    public synchronized void provideUnitClauses(UnitPropagationListener upl) {
        for (int i = 0; i < sharedUnitClauses.size(); i++) {
            upl.enqueue(sharedUnitClauses.get(i));
        }
    }

    public void setUnitClauseProvider(UnitClauseProvider ucp) {
        throw new UnsupportedOperationException(
                "Does not make sense in the parallel context");

    }

    public IConstr addConstr(Constr constr) {
        throw new UnsupportedOperationException(
                "Not implemented yet in ManyCore: cannot add a specific constraint to each solver");
    }

    public IConstr addParity(IVecInt literals, boolean even) {
        ConstrGroup group = new ConstrGroup(false);
        for (int i = 0; i < this.numberOfSolvers; i++) {
            group.add(this.solvers.get(i).addParity(literals, even));
        }
        return group;
    }

    public int getWinnerId() {
        checkWinnerId();
        return winnerId;
    }

    public AssignmentOrigin getOriginInModel(int p) {
        return this.solvers.get(getWinnerId()).getOriginInModel(p);
    }

    @Override
    public void setUnitClauseConsumer(UnitClauseConsumer ucc) {
        throw new UnsupportedOperationException(
                "Does not make sense in the parallel context");
    }

    @Override
    public int[] decisions() {
        return this.solvers.get(this.getWinnerId()).decisions();
    }
}

class RunnableSolver implements Runnable {

    private final int index;
    private final ISolver solver;
    private final OutcomeListener ol;
    private final IVecInt assumps;
    private final boolean globalTimeout;

    public RunnableSolver(int i, ISolver solver, IVecInt assumps,
            boolean globalTimeout, OutcomeListener ol) {
        this.index = i;
        this.solver = solver;
        this.ol = ol;
        this.assumps = assumps;
        this.globalTimeout = globalTimeout;
    }

    public void run() {
        try {
            boolean result = this.solver.isSatisfiable(this.assumps,
                    this.globalTimeout);
            this.ol.onFinishWithAnswer(true, result, this.index);
        } catch (Exception e) {
            this.ol.onFinishWithAnswer(false, false, this.index);
        }
    }

}
