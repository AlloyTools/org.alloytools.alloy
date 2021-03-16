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
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.specs.UnitClauseProvider;

public abstract class AbstractOutputSolver implements ISolver {

    protected int nbvars;

    protected int nbclauses;

    protected boolean fixedNbClauses = false;

    protected boolean firstConstr = true;

    private boolean verbose;

    /**
	 * 
	 */
    private static final long serialVersionUID = 1L;

    public boolean removeConstr(IConstr c) {
        throw new UnsupportedOperationException();
    }

    public void addAllClauses(IVec<IVecInt> clauses)
            throws ContradictionException {
        throw new UnsupportedOperationException();
    }

    public void setTimeout(int t) {
        // TODO Auto-generated method stub

    }

    public void setTimeoutMs(long t) {
        // TODO Auto-generated method stub
    }

    public int getTimeout() {
        return 0;
    }

    /**
     * @since 2.1
     */
    public long getTimeoutMs() {
        return 0L;
    }

    public void expireTimeout() {
        // TODO Auto-generated method stub

    }

    public boolean isSatisfiable(IVecInt assumps, boolean global)
            throws TimeoutException {
        throw new TimeoutException("There is no real solver behind!");
    }

    public boolean isSatisfiable(boolean global) throws TimeoutException {
        throw new TimeoutException("There is no real solver behind!");
    }

    public void printInfos(PrintWriter output, String prefix) {
    }

    public void setTimeoutOnConflicts(int count) {

    }

    public boolean isDBSimplificationAllowed() {
        return false;
    }

    public void setDBSimplificationAllowed(boolean status) {

    }

    public void printStat(PrintStream output, String prefix) {
        // TODO Auto-generated method stub
    }

    public void printStat(PrintWriter output, String prefix) {
        // TODO Auto-generated method stub

    }

    public Map<String, Number> getStat() {
        // TODO Auto-generated method stub
        return null;
    }

    public void clearLearntClauses() {
        // TODO Auto-generated method stub

    }

    public int[] model() {
        throw new UnsupportedOperationException();
    }

    public boolean model(int var) {
        throw new UnsupportedOperationException();
    }

    public boolean isSatisfiable() throws TimeoutException {
        throw new TimeoutException("There is no real solver behind!");
    }

    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        throw new TimeoutException("There is no real solver behind!");
    }

    public int[] findModel() throws TimeoutException {
        throw new UnsupportedOperationException();
    }

    public int[] findModel(IVecInt assumps) throws TimeoutException {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.1
     */
    public boolean removeSubsumedConstr(IConstr c) {
        return false;
    }

    /**
     * @since 2.1
     */
    public IConstr addBlockingClause(IVecInt literals)
            throws ContradictionException {
        throw new UnsupportedOperationException();
    }

    public IConstr discardCurrentModel() throws ContradictionException {
        throw new UnsupportedOperationException();
    }

    public IVecInt createBlockingClauseForCurrentModel() {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.2
     */
    public <S extends ISolverService> SearchListener<S> getSearchListener() {
        return null;
    }

    /**
     * @since 2.1
     */
    public <S extends ISolverService> void setSearchListener(
            SearchListener<S> sl) {
    }

    /**
     * @since 2.2
     */
    public boolean isVerbose() {
        return this.verbose;
    }

    /**
     * @since 2.2
     */
    public void setVerbose(boolean value) {
        this.verbose = value;
    }

    /**
     * @since 2.2
     */
    public void setLogPrefix(String prefix) {
        // do nothing

    }

    /**
     * @since 2.2
     */
    public String getLogPrefix() {
        return "";
    }

    /**
     * @since 2.2
     */
    public IVecInt unsatExplanation() {
        throw new UnsupportedOperationException();
    }

    public int[] primeImplicant() {
        throw new UnsupportedOperationException();
    }

    public int nConstraints() {
        // TODO Auto-generated method stub
        return 0;
    }

    public int newVar(int howmany) {
        // TODO Auto-generated method stub
        return 0;
    }

    public int nVars() {
        // TODO Auto-generated method stub
        return 0;
    }

    public boolean isSolverKeptHot() {
        return false;
    }

    public void setKeepSolverHot(boolean value) {
    }

    public ISolver getSolvingEngine() {
        throw new UnsupportedOperationException();
    }

    public void setUnitClauseProvider(UnitClauseProvider upl) {
        throw new UnsupportedOperationException();
    }

    public IConstr addConstr(Constr constr) {
        throw new UnsupportedOperationException();
    }
}
