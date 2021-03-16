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
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
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
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.specs.UnitClauseConsumer;
import org.sat4j.specs.UnitClauseProvider;

@Feature("solver")
public class StatisticsSolver implements ISolver {

    private static final String NOT_IMPLEMENTED_YET = "Not implemented yet!";

    private static final String THAT_SOLVER_ONLY_COMPUTE_STATISTICS = "That solver only compute statistics";

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Number of constraints in the problem
     */
    private int expectedNumberOfConstraints;

    /**
     * Number of declared vars (max var id)
     */
    private int nbvars;

    /**
     * Size of the constraints for each occurrence of each var for each polarity
     */
    private IVecInt[] sizeoccurrences;

    private int binarynegative = 0;

    private int binarypositive = 0;

    private int allpositive = 0;

    private int allnegative = 0;

    private int horn = 0;

    private int dualhorn = 0;

    /**
     * Distribution of clauses size
     */
    private final Map<Integer, Counter> sizes = new HashMap<Integer, Counter>();

    public int[] model() {
        throw new UnsupportedOperationException(
                THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean model(int var) {
        throw new UnsupportedOperationException(
                THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public int[] primeImplicant() {
        throw new UnsupportedOperationException(
                THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean primeImplicant(int p) {
        throw new UnsupportedOperationException(
                THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean isSatisfiable() throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean isSatisfiable(IVecInt assumps, boolean globalTimeout)
            throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean isSatisfiable(boolean globalTimeout)
            throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public int[] findModel() throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public int[] findModel(IVecInt assumps) throws TimeoutException {
        throw new TimeoutException(THAT_SOLVER_ONLY_COMPUTE_STATISTICS);
    }

    public int nConstraints() {
        return expectedNumberOfConstraints;
    }

    public int newVar(int howmany) {
        this.nbvars = howmany;
        sizeoccurrences = new IVecInt[(howmany + 1) << 1];
        return howmany;
    }

    public int nVars() {
        return this.nbvars;
    }

    @Deprecated
    public void printInfos(PrintWriter out, String prefix) {

    }

    public void printInfos(PrintWriter out) {
    }

    @Deprecated
    public int newVar() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public int nextFreeVarId(boolean reserve) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void registerLiteral(int p) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setExpectedNumberOfClauses(int nb) {
        this.expectedNumberOfConstraints = nb;
    }

    public IConstr addClause(IVecInt literals) throws ContradictionException {
        int size = literals.size();
        Counter counter = sizes.get(size);
        if (counter == null) {
            counter = new Counter(0);
            sizes.put(size, counter);
        }
        counter.inc();
        IVecInt list;
        int x, p;
        int pos = 0, neg = 0;
        for (IteratorInt it = literals.iterator(); it.hasNext();) {
            x = it.next();
            if (x > 0) {
                pos++;
            } else {
                neg++;
            }
            p = LiteralsUtils.toInternal(x);
            list = sizeoccurrences[p];
            if (list == null) {
                list = new VecInt();
                sizeoccurrences[p] = list;
            }
            list.push(size);
        }
        if (neg == 0) {
            allpositive++;
            if (size == 2) {
                binarypositive++;
            }
        } else if (pos == 0) {
            allnegative++;
            if (size == 2) {
                binarynegative++;
            }
        } else if (pos == 1) {
            horn++;
        } else if (neg == 1) {
            dualhorn++;
        }
        return null;
    }

    public IConstr addBlockingClause(IVecInt literals)
            throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr discardCurrentModel() throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IVecInt createBlockingClauseForCurrentModel() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public boolean removeConstr(IConstr c) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public boolean removeSubsumedConstr(IConstr c) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void addAllClauses(IVec<IVecInt> clauses)
            throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setTimeout(int t) {
    }

    public void setTimeoutOnConflicts(int count) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setTimeoutMs(long t) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public int getTimeout() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public long getTimeoutMs() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void expireTimeout() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void reset() {
    }

    @Deprecated
    public void printStat(PrintStream out, String prefix) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    @Deprecated
    public void printStat(PrintWriter out, String prefix) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void printStat(PrintWriter out) {
        int realNumberOfVariables = 0;
        int realNumberOfLiterals = 0;
        int pureLiterals = 0;
        int minOccV = Integer.MAX_VALUE;
        int maxOccV = Integer.MIN_VALUE;
        int sumV = 0;
        int sizeL, sizeV;
        int minOccL = Integer.MAX_VALUE;
        int maxOccL = Integer.MIN_VALUE;
        int sumL = 0;
        IVecInt list;
        boolean oneNull;
        if (sizeoccurrences == null) {
            return;
        }
        int max = sizeoccurrences.length - 1;
        for (int i = 2; i < max; i += 2) {
            sizeV = 0;
            oneNull = false;
            for (int k = 0; k < 2; k++) {
                list = sizeoccurrences[i + k];
                if (list == null) {
                    oneNull = true;
                } else {
                    realNumberOfLiterals++;
                    sizeL = list.size();
                    sizeV += sizeL;
                    if (minOccL > sizeL) {
                        minOccL = sizeL;
                    }
                    if (sizeL > maxOccL) {
                        maxOccL = sizeL;
                    }
                    sumL += sizeL;
                }
            }

            if (sizeV > 0) {
                if (oneNull) {
                    pureLiterals++;
                }
                realNumberOfVariables++;
                if (minOccV > sizeV) {
                    minOccV = sizeV;
                }
                if (sizeV > maxOccV) {
                    maxOccV = sizeV;
                }
                sumV += sizeV;
            }

        }
        if (realNumberOfVariables > 0 && realNumberOfLiterals > 0) {
            System.out.println("c Distribution of constraints size:");
            int nbclauses = 0;
            for (Map.Entry<Integer, Counter> entry : sizes.entrySet()) {
                System.out.printf("c %d => %d%n", entry.getKey(),
                        entry.getValue().getValue());
                nbclauses += entry.getValue().getValue();
            }

            System.out.printf(
                    "c Real number of variables, literals, number of clauses, size (#literals), #pureliterals, ");
            System.out.printf("variable occurrences (min/max/avg) ");
            System.out.printf("literals occurrences (min/max/avg) ");
            System.out.println(
                    "Specific clauses: #positive  #negative #horn  #dualhorn #binary #binarynegative #binarypositive #binaryhorn #remaining");
            Counter binaryCounter = sizes.get(2);
            int nbBinary = binaryCounter == null ? 0 : binaryCounter.getValue();
            System.out.printf(Locale.US,
                    "%d %d %d %d %d %d %d %.2f %d %d %.2f ",
                    realNumberOfVariables, realNumberOfLiterals, nbclauses,
                    sumL, pureLiterals, minOccV, maxOccV,
                    sumV / (realNumberOfVariables * 1.0), minOccL, maxOccL,
                    sumL / (realNumberOfLiterals * 1.0));
            System.out.printf("%d %d %d %d %d %d %d %d %d%n", allpositive,
                    allnegative, horn, dualhorn, nbBinary, binarynegative,
                    binarypositive,
                    (nbBinary - binarynegative - binarypositive),
                    nbclauses - allpositive - allnegative - horn - dualhorn);
        }
    }

    public Map<String, Number> getStat() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public String toString(String prefix) {
        return prefix + "Statistics about the benchmarks";
    }

    public void clearLearntClauses() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setDBSimplificationAllowed(boolean status) {
    }

    public boolean isDBSimplificationAllowed() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public <S extends ISolverService> void setSearchListener(
            SearchListener<S> sl) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public <S extends ISolverService> SearchListener<S> getSearchListener() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public boolean isVerbose() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setVerbose(boolean value) {
    }

    public void setLogPrefix(String prefix) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public String getLogPrefix() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IVecInt unsatExplanation() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public int[] modelWithInternalVariables() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public int realNumberOfVariables() {
        return nbvars;
    }

    public boolean isSolverKeptHot() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setKeepSolverHot(boolean keepHot) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public ISolver getSolvingEngine() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public void setUnitClauseProvider(UnitClauseProvider ucp) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr addConstr(Constr constr) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public IConstr addParity(IVecInt literals, boolean even) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    public AssignmentOrigin getOriginInModel(int p) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    @Override
    public void setUnitClauseConsumer(UnitClauseConsumer ucc) {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }

    @Override
    public int[] decisions() {
        throw new UnsupportedOperationException(NOT_IMPLEMENTED_YET);
    }
}
