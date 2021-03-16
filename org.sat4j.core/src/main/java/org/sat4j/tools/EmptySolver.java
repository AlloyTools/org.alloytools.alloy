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

import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.FakeConstr;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.specs.UnitClauseProvider;

/**
 * Empty solver meant to be specialized to be used instead of real solvers
 * inside e.g. parsers.
 * 
 * 
 * @author leberre
 * @since 2.3.6
 */
public abstract class EmptySolver implements ISolver {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final IConstr FAKECONSTR = FakeConstr.instance();

    private int nbVars;

    private int nbClauses;

    public int[] model() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int[] primeImplicant() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean primeImplicant(int p) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfiable() throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfiable(IVecInt assumps, boolean globalTimeout)
            throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfiable(boolean globalTimeout)
            throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int[] findModel() throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int[] findModel(IVecInt assumps) throws TimeoutException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int nConstraints() {
        return nbClauses;
    }

    public int newVar(int howmany) {
        this.nbVars = howmany;
        return howmany;
    }

    public int nVars() {
        return nbVars;
    }

    public void printInfos(PrintWriter out, String prefix) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void printInfos(PrintWriter out) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean model(int var) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int newVar() {
        nbVars++;
        return nbVars;
    }

    public int nextFreeVarId(boolean reserve) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void registerLiteral(int p) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void setExpectedNumberOfClauses(int nb) {
        this.nbClauses = nb;
    }

    public IConstr addClause(IVecInt literals) throws ContradictionException {
        return FAKECONSTR;
    }

    public IConstr addBlockingClause(IVecInt literals)
            throws ContradictionException {
        return FAKECONSTR;
    }

    public IConstr discardCurrentModel() throws ContradictionException {
        return FAKECONSTR;
    }

    public IVecInt createBlockingClauseForCurrentModel() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean removeConstr(IConstr c) {
        return false;
    }

    public boolean removeSubsumedConstr(IConstr c) {
        return false;
    }

    public void addAllClauses(IVec<IVecInt> clauses)
            throws ContradictionException {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        return FAKECONSTR;
    }

    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        return FAKECONSTR;
    }

    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        return FAKECONSTR;
    }

    public IConstr addConstr(Constr constr) {
        return FAKECONSTR;
    }

    public void setTimeout(int t) {

    }

    public void setTimeoutOnConflicts(int count) {

    }

    public void setTimeoutMs(long t) {

    }

    public int getTimeout() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public long getTimeoutMs() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void expireTimeout() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void reset() {

    }

    public void printStat(PrintStream out, String prefix) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void printStat(PrintWriter out, String prefix) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void printStat(PrintWriter out) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public Map<String, Number> getStat() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public String toString(String prefix) {
        return "Empty Solver";
    }

    public void clearLearntClauses() {

    }

    public void setDBSimplificationAllowed(boolean status) {

    }

    public boolean isDBSimplificationAllowed() {
        return false;
    }

    public <S extends ISolverService> void setSearchListener(
            SearchListener<S> sl) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void setUnitClauseProvider(UnitClauseProvider ucp) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public <S extends ISolverService> SearchListener<S> getSearchListener() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isVerbose() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void setVerbose(boolean value) {

    }

    public void setLogPrefix(String prefix) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public String getLogPrefix() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public IVecInt unsatExplanation() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int[] modelWithInternalVariables() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int realNumberOfVariables() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSolverKeptHot() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void setKeepSolverHot(boolean keepHot) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public ISolver getSolvingEngine() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

}
