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
import java.io.Serializable;
import java.util.Random;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;

/**
 * @since 2.2
 */
@Feature(value = "varheuristics", parent = "expert")
public class RandomWalkDecorator implements IOrder, Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final VarOrderHeap decorated;

    private double p;

    private static final Random RAND = System
            .getProperty("NONDETERMINISTIC") == null ? new Random(123456789)
                    : new Random();
    private ILits voc;
    private int nbRandomWalks;

    public RandomWalkDecorator(VarOrderHeap order) {
        this(order, 0.01);
    }

    public RandomWalkDecorator(VarOrderHeap order, double p) {
        this.decorated = order;
        this.p = p;
    }

    public void assignLiteral(int q) {
        this.decorated.assignLiteral(q);
    }

    public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
        return this.decorated.getPhaseSelectionStrategy();
    }

    public double getProbability() {
        return this.p;
    }

    public void setProbability(double p) {
        this.p = p;
    }

    public void init() {
        this.decorated.init();
    }

    public void printStat(PrintWriter out, String prefix) {
        out.println(prefix + "random walks\t: " + this.nbRandomWalks);
        this.decorated.printStat(out, prefix);
    }

    public int select() {
        if (RAND.nextDouble() < this.p) {
            int var, lit, max;

            while (!this.decorated.heap.empty()) {
                max = this.decorated.heap.size();
                var = this.decorated.heap.get(RAND.nextInt(max) + 1);
                lit = getPhaseSelectionStrategy().select(var);
                if (this.voc.isUnassigned(lit)) {
                    this.nbRandomWalks++;
                    return lit;
                }
            }
        }
        return this.decorated.select();
    }

    public void setLits(ILits lits) {
        this.decorated.setLits(lits);
        this.voc = lits;
        this.nbRandomWalks = 0;
    }

    public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
        this.decorated.setPhaseSelectionStrategy(strategy);
    }

    public void setVarDecay(double d) {
        this.decorated.setVarDecay(d);
    }

    public void undo(int x) {
        this.decorated.undo(x);
    }

    public void updateVar(int q) {
        this.decorated.updateVar(q);
    }

    @Override
    public void updateVar(int p, double value) {
        updateVar(p);
    }

    public double varActivity(int q) {
        return this.decorated.varActivity(q);
    }

    public void varDecayActivity() {
        this.decorated.varDecayActivity();
    }

    public void updateVarAtDecisionLevel(int q) {
        this.decorated.updateVarAtDecisionLevel(q);
    }

    @Override
    public String toString() {
        return this.decorated.toString() + " with random walks " + this.p;
    }

    public double[] getVariableHeuristics() {
        return this.decorated.getVariableHeuristics();
    }

}
