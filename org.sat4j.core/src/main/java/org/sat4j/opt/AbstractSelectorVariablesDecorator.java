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

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.SolverDecorator;

/**
 * Abstract class which adds a new "selector" variable for each clause entered
 * in the solver.
 * 
 * As a consequence, an original problem with n variables and m clauses will end
 * up with n+m variables.
 * 
 * @author daniel
 * 
 */
public abstract class AbstractSelectorVariablesDecorator extends
        SolverDecorator<ISolver> implements IOptimizationProblem {

    /**
	 * 
	 */
    private static final long serialVersionUID = 1L;

    private int nbexpectedclauses;

    private int[] prevfullmodel;

    /**
     * @since 2.1
     */
    private int[] prevmodel;
    /**
     * @since 2.1
     */
    private boolean[] prevboolmodel;

    private boolean isSolutionOptimal;

    /**
     * @since 2.3.6
     */
    private IVecInt prevBlockingClause;

    public AbstractSelectorVariablesDecorator(ISolver solver) {
        super(solver);
    }

    @Override
    public void setExpectedNumberOfClauses(int nb) {
        this.nbexpectedclauses = nb;
    }

    public int getExpectedNumberOfClauses() {
        return this.nbexpectedclauses;
    }

    public boolean admitABetterSolution() throws TimeoutException {
        return admitABetterSolution(VecInt.EMPTY);
    }

    /**
     * @since 2.1
     */
    public boolean admitABetterSolution(IVecInt assumps)
            throws TimeoutException {
        this.isSolutionOptimal = false;
        boolean result = super.isSatisfiable(assumps, true);
        if (result) {
            this.prevboolmodel = new boolean[nVars()];
            for (int i = 0; i < nVars(); i++) {
                this.prevboolmodel[i] = decorated().model(i + 1);
            }
            this.prevfullmodel = super.modelWithInternalVariables();
            this.prevmodel = super.model();
            this.prevBlockingClause = super
                    .createBlockingClauseForCurrentModel();
            calculateObjectiveValue();
        } else {
            this.isSolutionOptimal = true;
        }
        return result;
    }

    abstract void calculateObjectiveValue();

    @Override
    public int[] model() {
        return this.prevmodel;
    }

    @Override
    public boolean model(int var) {
        return this.prevboolmodel[var - 1];
    }

    @Override
    public IConstr discardCurrentModel() throws ContradictionException {
        return addBlockingClause(this.prevBlockingClause);
    }

    @Override
    public IVecInt createBlockingClauseForCurrentModel() {
        return this.prevBlockingClause;
    }

    public boolean isOptimal() {
        return this.isSolutionOptimal;
    }

    public int getNbexpectedclauses() {
        return nbexpectedclauses;
    }

    public void setNbexpectedclauses(int nbexpectedclauses) {
        this.nbexpectedclauses = nbexpectedclauses;
    }

    public int[] getPrevfullmodel() {
        return prevfullmodel;
    }

    public void setPrevfullmodel(int[] prevfullmodel) {
        this.prevfullmodel = prevfullmodel.clone();
    }

    public int[] getPrevmodel() {
        return prevmodel;
    }

    public void setPrevmodel(int[] prevmodel) {
        this.prevmodel = prevmodel.clone();
    }

    public boolean[] getPrevboolmodel() {
        return prevboolmodel;
    }

    public void setPrevboolmodel(boolean[] prevboolmodel) {
        this.prevboolmodel = prevboolmodel.clone();
    }

    public boolean isSolutionOptimal() {
        return isSolutionOptimal;
    }

    public void setSolutionOptimal(boolean isSolutionOptimal) {
        this.isSolutionOptimal = isSolutionOptimal;
    }
}
