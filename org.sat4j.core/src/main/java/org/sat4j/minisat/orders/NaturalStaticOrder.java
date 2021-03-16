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
package org.sat4j.minisat.orders;

import java.io.PrintWriter;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;

/**
 * Static ordering of the decisions based on the natural order of the variables.
 * 
 * It is not meant to be efficient but to allow to easily study the behavior of
 * the solver on a known order of the decisions.
 * 
 * @author leberre
 *
 */
@Feature(value = "varheuristics", parent = "expert")
public class NaturalStaticOrder implements IOrder {

    private ILits voc;

    private IPhaseSelectionStrategy phaseSelectionStrategy = new NegativeLiteralSelectionStrategy();

    int index;

    @Override
    public void setLits(ILits lits) {
        this.voc = lits;
    }

    @Override
    public int select() {
        while (!voc.isUnassigned(LiteralsUtils.posLit(index))
                || !voc.belongsToPool(index)) {
            index++;
            if (index > voc.nVars()) {
                return ILits.UNDEFINED;
            }
        }
        return phaseSelectionStrategy.select(index);
    }

    @Override
    public void undo(int x) {
        index = Math.min(index, x);
    }

    @Override
    public void updateVar(int p) {
    }

    @Override
    public void updateVar(int p, double value) {
        updateVar(p);
    }

    @Override
    public void init() {
        index = 1;
    }

    @Override
    public void printStat(PrintWriter out, String prefix) {
    }

    @Override
    public void setVarDecay(double d) {
    }

    @Override
    public void varDecayActivity() {
    }

    @Override
    public double varActivity(int p) {
        return 0.0d;
    }

    @Override
    public void assignLiteral(int p) {
    }

    @Override
    public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
        this.phaseSelectionStrategy = strategy;
    }

    @Override
    public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
        return this.phaseSelectionStrategy;
    }

    @Override
    public void updateVarAtDecisionLevel(int q) {
    }

    @Override
    public double[] getVariableHeuristics() {
        return new double[0];
    }

    @Override
    public String toString() {
        return "Natural static ordering";
    }
}
