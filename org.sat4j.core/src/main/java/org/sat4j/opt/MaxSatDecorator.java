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
package org.sat4j.opt;

import org.sat4j.annotations.Feature;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Computes a solution that satisfies the maximum of clauses.
 * 
 * @author daniel
 * 
 */
@Feature("solver")
public final class MaxSatDecorator extends AbstractSelectorVariablesDecorator {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final boolean equivalence;

    public MaxSatDecorator(ISolver solver) {
        this(solver, false);
    }

    public MaxSatDecorator(ISolver solver, boolean equivalence) {
        super(solver);
        this.equivalence = equivalence;
    }

    @Override
    public void setExpectedNumberOfClauses(int nb) {
        super.setExpectedNumberOfClauses(nb);
        this.lits.ensure(nb);
    }

    @Override
    public IConstr addClause(IVecInt literals) throws ContradictionException {
        int newvar = nextFreeVarId(true);
        this.lits.push(newvar);
        literals.push(newvar);
        if (this.equivalence) {
            ConstrGroup constrs = new ConstrGroup();
            constrs.add(super.addClause(literals));
            IVecInt clause = new VecInt(2);
            clause.push(-newvar);
            for (int i = 0; i < literals.size() - 1; i++) {
                clause.push(-literals.get(i));
                constrs.add(super.addClause(clause));
            }
            clause.pop();
            return constrs;
        }
        return super.addClause(literals);
    }

    @Override
    public void reset() {
        this.lits.clear();
        super.reset();
        this.prevConstr = null;
    }

    public boolean hasNoObjectiveFunction() {
        return false;
    }

    public boolean nonOptimalMeansSatisfiable() {
        return false;
    }

    public Number calculateObjective() {
        calculateObjectiveValue();
        return this.counter;
    }

    private final IVecInt lits = new VecInt();

    private int counter;

    private IConstr prevConstr;

    /**
     * @since 2.1
     */
    public void discardCurrentSolution() throws ContradictionException {
        if (this.prevConstr != null) {
            super.removeSubsumedConstr(this.prevConstr);
        }
        try {
            this.prevConstr = super.addAtMost(this.lits, this.counter - 1);
        } catch (ContradictionException ce) {
            setSolutionOptimal(true);
            throw ce;
        }
    }

    @Override
    public boolean admitABetterSolution(IVecInt assumps)
            throws TimeoutException {

        boolean result = super.admitABetterSolution(assumps);
        if (!result && this.prevConstr != null) {
            super.removeConstr(this.prevConstr);
            this.prevConstr = null;
        }
        return result;
    }

    public void discard() throws ContradictionException {
        discardCurrentSolution();
    }

    /**
     * @since 2.1
     */
    public Number getObjectiveValue() {
        return this.counter;
    }

    @Override
    void calculateObjectiveValue() {
        this.counter = 0;
        for (int q : getPrevfullmodel()) {
            if (q > nVars()) {
                this.counter++;
            }
        }
    }

    /**
     * @since 2.1
     */
    public void forceObjectiveValueTo(Number forcedValue)
            throws ContradictionException {
        super.addAtMost(this.lits, forcedValue.intValue());
    }

    public void setTimeoutForFindingBetterSolution(int seconds) {
        // TODO
        throw new UnsupportedOperationException("No implemented yet");
    }
}
