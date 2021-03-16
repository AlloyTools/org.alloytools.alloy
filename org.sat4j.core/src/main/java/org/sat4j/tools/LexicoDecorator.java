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

import java.util.ArrayList;
import java.util.List;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;

@Feature("solver")
public class LexicoDecorator<T extends ISolver> extends SolverDecorator<T>
        implements IOptimizationProblem {

    protected final List<IVecInt> criteria = new ArrayList<IVecInt>();

    protected int currentCriterion = 0;

    protected IConstr prevConstr;

    private Number currentValue = -1;

    protected int[] prevfullmodel;
    protected int[] prevmodelwithinternalvars;
    protected boolean[] prevboolmodel;

    protected boolean isSolutionOptimal;

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public LexicoDecorator(T solver) {
        super(solver);
    }

    public void addCriterion(IVecInt literals) {
        IVecInt copy = new VecInt(literals.size());
        literals.copyTo(copy);
        this.criteria.add(copy);
    }

    public boolean admitABetterSolution() throws TimeoutException {
        return admitABetterSolution(VecInt.EMPTY);
    }

    public boolean admitABetterSolution(IVecInt assumps)
            throws TimeoutException {
        this.isSolutionOptimal = false;
        if (decorated().isSatisfiable(assumps, true)) {
            this.prevboolmodel = new boolean[nVars()];
            for (int i = 0; i < nVars(); i++) {
                this.prevboolmodel[i] = decorated().model(i + 1);
            }
            this.prevfullmodel = decorated().model();
            this.prevmodelwithinternalvars = decorated()
                    .modelWithInternalVariables();
            calculateObjective();
            return true;
        }
        return manageUnsatCase();
    }

    protected boolean manageUnsatCase() {
        if (this.prevfullmodel == null) {
            // the problem is UNSAT
            return false;
        }
        // an optimal solution has been found
        // for one criteria
        if (this.currentCriterion < numberOfCriteria() - 1) {
            if (this.prevConstr != null) {
                super.removeConstr(this.prevConstr);
                this.prevConstr = null;
            }
            try {
                fixCriterionValue();
            } catch (ContradictionException e) {
                throw new IllegalStateException(e);
            }
            if (isVerbose()) {
                System.out.println(
                        getLogPrefix() + "Found optimal criterion number "
                                + (this.currentCriterion + 1));
            }
            this.currentCriterion++;
            calculateObjective();
            return true;
        }
        if (isVerbose()) {
            System.out.println(getLogPrefix()
                    + "Found optimal solution for the last criterion ");
        }
        this.isSolutionOptimal = true;
        if (this.prevConstr != null) {
            super.removeConstr(this.prevConstr);
            this.prevConstr = null;
        }
        return false;
    }

    public int numberOfCriteria() {
        return this.criteria.size();
    }

    protected void fixCriterionValue() throws ContradictionException {
        super.addExactly(this.criteria.get(this.currentCriterion),
                this.currentValue.intValue());
    }

    @Override
    public int[] model() {
        return this.prevfullmodel;
    }

    @Override
    public boolean model(int var) {
        return this.prevboolmodel[var - 1];
    }

    @Override
    public int[] modelWithInternalVariables() {
        return this.prevmodelwithinternalvars;
    }

    public boolean hasNoObjectiveFunction() {
        return false;
    }

    public boolean nonOptimalMeansSatisfiable() {
        return true;
    }

    public Number calculateObjective() {
        this.currentValue = evaluate();
        return this.currentValue;
    }

    public Number getObjectiveValue() {
        return this.currentValue;
    }

    public Number getObjectiveValue(int criterion) {
        return evaluate(criterion);
    }

    public void forceObjectiveValueTo(Number forcedValue)
            throws ContradictionException {
        throw new UnsupportedOperationException();
    }

    public void discard() throws ContradictionException {
        discardCurrentSolution();

    }

    public void discardCurrentSolution() throws ContradictionException {
        if (this.prevConstr != null) {
            super.removeSubsumedConstr(this.prevConstr);
        }
        try {
            this.prevConstr = discardSolutionsForOptimizing();
        } catch (ContradictionException c) {
            this.prevConstr = null;
            if (!manageUnsatCase()) {
                throw c;
            }
        }

    }

    protected IConstr discardSolutionsForOptimizing()
            throws ContradictionException {
        return super.addAtMost(this.criteria.get(this.currentCriterion),
                this.currentValue.intValue() - 1);
    }

    protected Number evaluate() {
        return evaluate(this.currentCriterion);
    }

    protected Number evaluate(int criterion) {
        int value = 0;
        int lit;
        for (IteratorInt it = this.criteria.get(this.currentCriterion)
                .iterator(); it.hasNext();) {
            lit = it.next();
            if (lit > 0 && this.prevboolmodel[lit - 1]
                    || lit < 0 && !this.prevboolmodel[-lit - 1]) {
                value++;
            }
        }
        return value;
    }

    public boolean isOptimal() {
        return this.isSolutionOptimal;
    }

    public void setTimeoutForFindingBetterSolution(int seconds) {
        // TODO
        throw new UnsupportedOperationException("No implemented yet");
    }

}
