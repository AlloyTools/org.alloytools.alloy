/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
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
import java.util.Map;

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

/**
 * The aim of that class is to allow adding dynamic responsibilities to SAT
 * solvers using the Decorator design pattern. The class is abstract because it
 * does not makes sense to use it "as is".
 * 
 * @author leberre
 */
public abstract class SolverDecorator<T extends ISolver> implements ISolver {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public boolean isDBSimplificationAllowed() {
        return this.solver.isDBSimplificationAllowed();
    }

    public void setDBSimplificationAllowed(boolean status) {
        this.solver.setDBSimplificationAllowed(status);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#setTimeoutOnConflicts(int)
     */
    public void setTimeoutOnConflicts(int count) {
        this.solver.setTimeoutOnConflicts(count);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#printInfos(java.io.PrintWriter,
     * java.lang.String)
     */
    public void printInfos(PrintWriter out, String prefix) {
        this.solver.printInfos(out, prefix);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#printInfos(java.io.PrintWriter,
     * java.lang.String)
     */
    public void printInfos(PrintWriter out) {
        this.solver.printInfos(out);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#isSatisfiable(boolean)
     */
    public boolean isSatisfiable(boolean global) throws TimeoutException {
        return this.solver.isSatisfiable(global);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#isSatisfiable(org.sat4j.specs.IVecInt,
     * boolean)
     */
    public boolean isSatisfiable(IVecInt assumps, boolean global)
            throws TimeoutException {
        return this.solver.isSatisfiable(assumps, global);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#clearLearntClauses()
     */
    public void clearLearntClauses() {
        this.solver.clearLearntClauses();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#findModel()
     */
    public int[] findModel() throws TimeoutException {
        return this.solver.findModel();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#findModel(org.sat4j.specs.IVecInt)
     */
    public int[] findModel(IVecInt assumps) throws TimeoutException {
        return this.solver.findModel(assumps);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.IProblem#model(int)
     */
    public boolean model(int var) {
        return this.solver.model(var);
    }

    public void setExpectedNumberOfClauses(int nb) {
        this.solver.setExpectedNumberOfClauses(nb);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#getTimeout()
     */
    public int getTimeout() {
        return this.solver.getTimeout();
    }

    /**
     * @since 2.1
     */
    public long getTimeoutMs() {
        return this.solver.getTimeoutMs();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#toString(java.lang.String)
     */
    public String toString(String prefix) {
        return this.solver.toString(prefix);
    }

    @Override
    public String toString() {
        return this.solver.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#printStat(java.io.PrintStream,
     * java.lang.String)
     */
    @Deprecated
    public void printStat(PrintStream out, String prefix) {
        this.solver.printStat(out, prefix);
    }

    public void printStat(PrintWriter out, String prefix) {
        this.solver.printStat(out, prefix);
    }

    public void printStat(PrintWriter out) {
        this.solver.printStat(out);
    }

    private T solver;

    /**
     * 
     */
    public SolverDecorator(T solver) {
        this.solver = solver;
    }

    @Deprecated
    public int newVar() {
        return this.solver.newVar();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#newVar(int)
     */
    public int newVar(int howmany) {
        return this.solver.newVar(howmany);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#addClause(org.sat4j.datatype.VecInt)
     */
    public IConstr addClause(IVecInt literals) throws ContradictionException {
        return this.solver.addClause(literals);
    }

    public void addAllClauses(IVec<IVecInt> clauses)
            throws ContradictionException {
        this.solver.addAllClauses(clauses);
    }

    /**
     * @since 2.1
     */
    public IConstr addBlockingClause(IVecInt literals)
            throws ContradictionException {
        return this.solver.addBlockingClause(literals);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#discardCurrentModel()
     */
    public IConstr discardCurrentModel() throws ContradictionException {
        return this.solver.discardCurrentModel();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#createBlockingClauseForCurrentModel()
     */
    public IVecInt createBlockingClauseForCurrentModel() {
        return this.solver.createBlockingClauseForCurrentModel();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#addAtMost(org.sat4j.datatype.VecInt, int)
     */
    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        return this.solver.addAtMost(literals, degree);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#addAtLeast(org.sat4j.datatype.VecInt, int)
     */
    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        return this.solver.addAtLeast(literals, degree);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#model()
     */
    public int[] model() {
        return this.solver.model();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#isSatisfiable()
     */
    public boolean isSatisfiable() throws TimeoutException {
        return this.solver.isSatisfiable();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#isSatisfiable(org.sat4j.datatype.VecInt)
     */
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        return this.solver.isSatisfiable(assumps);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#setTimeout(int)
     */
    public void setTimeout(int t) {
        this.solver.setTimeout(t);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#setTimeoutMs(int)
     */
    public void setTimeoutMs(long t) {
        this.solver.setTimeoutMs(t);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#expireTimeout()
     */
    public void expireTimeout() {
        this.solver.expireTimeout();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#nConstraints()
     */
    public int nConstraints() {
        return this.solver.nConstraints();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#nVars()
     */
    public int nVars() {
        return this.solver.nVars();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#reset()
     */
    public void reset() {
        this.solver.reset();
    }

    public T decorated() {
        return this.solver;
    }

    /**
     * Method to be called to clear the decorator from its decorated solver.
     * This is especially useful to avoid memory leak in a program.
     * 
     * @return the decorated solver.
     */
    public T clearDecorated() {
        T decorated = this.solver;
        this.solver = null;
        return decorated;
    }

    protected void setDecorated(T solver) {
        this.solver = solver;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#removeConstr(org.sat4j.minisat.core.Constr)
     */
    public boolean removeConstr(IConstr c) {
        return this.solver.removeConstr(c);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.specs.ISolver#getStat()
     */
    public Map<String, Number> getStat() {
        return this.solver.getStat();
    }

    /**
     * @since 2.1
     */
    public <S extends ISolverService> void setSearchListener(
            SearchListener<S> sl) {
        this.solver.setSearchListener(sl);
    }

    /**
     * @since 2.1
     */
    public int nextFreeVarId(boolean reserve) {
        return this.solver.nextFreeVarId(reserve);
    }

    /**
     * @since 2.1
     */
    public boolean removeSubsumedConstr(IConstr c) {
        return this.solver.removeSubsumedConstr(c);
    }

    /**
     * @since 2.2
     */
    public <S extends ISolverService> SearchListener<S> getSearchListener() {
        return this.solver.getSearchListener();
    }

    /**
     * @since 2.2
     */
    public boolean isVerbose() {
        return this.solver.isVerbose();
    }

    /**
     * @since 2.2
     */
    public void setVerbose(boolean value) {
        this.solver.setVerbose(value);
    }

    /**
     * @since 2.2
     */
    public void setLogPrefix(String prefix) {
        this.solver.setLogPrefix(prefix);
    }

    /**
     * @since 2.2
     */
    public String getLogPrefix() {
        return this.solver.getLogPrefix();
    }

    /**
     * @since 2.2
     */
    public IVecInt unsatExplanation() {
        return this.solver.unsatExplanation();
    }

    /**
     * @since 2.3
     */
    public int[] primeImplicant() {
        return this.solver.primeImplicant();
    }

    /**
     * @since 2.3.1
     */
    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        return this.solver.addExactly(literals, n);
    }

    /**
     * @since 2.3.1
     */
    public int[] modelWithInternalVariables() {
        return this.solver.modelWithInternalVariables();
    }

    /**
     * @since 2.3.1
     */
    public int realNumberOfVariables() {
        return this.solver.realNumberOfVariables();
    }

    /**
     * @since 2.3.1
     */
    public void registerLiteral(int p) {
        this.solver.registerLiteral(p);
    }

    /**
     * @since 2.3.2
     */
    public boolean isSolverKeptHot() {
        return this.solver.isSolverKeptHot();
    }

    /**
     * @since 2.3.2
     */
    public void setKeepSolverHot(boolean value) {
        this.solver.setKeepSolverHot(value);
    }

    /**
     * @since 2.3.2
     */
    public boolean primeImplicant(int p) {
        return this.solver.primeImplicant(p);
    }

    /**
     * @since 2.3.3
     */
    public ISolver getSolvingEngine() {
        return this.solver.getSolvingEngine();
    }

    /**
     * @since 2.3.4
     */
    public void setUnitClauseProvider(UnitClauseProvider ucp) {
        this.solver.setUnitClauseProvider(ucp);
    }

    /**
     * @since 2.3.6
     */
    public IConstr addConstr(Constr constr) {
        return this.solver.addConstr(constr);
    }

    /**
     * @since 2.3.6
     */
    public IConstr addParity(IVecInt literals, boolean even) {
        return this.solver.addParity(literals, even);
    }

    public AssignmentOrigin getOriginInModel(int p) {
        return this.solver.getOriginInModel(p);
    }

    @Override
    public void setUnitClauseConsumer(UnitClauseConsumer ucc) {
        this.solver.setUnitClauseConsumer(ucc);
    }

    @Override
    public int[] decisions() {
        return this.solver.decisions();
    }
}
