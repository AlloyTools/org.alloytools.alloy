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
import java.util.LinkedList;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;

/**
 * Uses a tabu list to prevent the solver to
 * 
 * @since 2.3.2
 */
@Feature(value = "varheuristics", parent = "expert")
public class TabuListDecorator implements IOrder {

    private final VarOrderHeap decorated;

    private final int tabuSize;

    private ILits voc;
    private int lastVar = -1;

    private final LinkedList<Integer> tabuList = new LinkedList<Integer>();

    public TabuListDecorator(VarOrderHeap order) {
        this(order, 10);
    }

    public TabuListDecorator(VarOrderHeap order, int tabuSize) {
        this.decorated = order;
        this.tabuSize = tabuSize;
    }

    public void assignLiteral(int q) {
        this.decorated.assignLiteral(q);
    }

    public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
        return this.decorated.getPhaseSelectionStrategy();
    }

    public void init() {
        this.decorated.init();
        this.lastVar = -1;
    }

    public void printStat(PrintWriter out, String prefix) {
        out.println(prefix + "tabu list size\t: " + this.tabuSize);
        this.decorated.printStat(out, prefix);
    }

    public int select() {
        int lit = this.decorated.select();
        if (lit == ILits.UNDEFINED) {
            int var;
            do {
                if (this.tabuList.isEmpty()) {
                    return ILits.UNDEFINED;
                }
                var = this.tabuList.removeFirst();
            } while (!this.voc.isUnassigned(var << 1));
            return getPhaseSelectionStrategy().select(var);
        }
        this.lastVar = lit >> 1;
        return lit;
    }

    public void setLits(ILits lits) {
        this.decorated.setLits(lits);
        this.voc = lits;
    }

    public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
        this.decorated.setPhaseSelectionStrategy(strategy);
    }

    public void setVarDecay(double d) {
        this.decorated.setVarDecay(d);
    }

    public void undo(int x) {
        if (this.tabuList.size() == this.tabuSize) {
            int var = this.tabuList.removeFirst();
            this.decorated.undo(var);
        }
        if (x == this.lastVar) {
            this.tabuList.add(x);
            this.lastVar = -1;
        } else {
            this.decorated.undo(x);
        }
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
        return this.decorated.toString() + " with tabu list of size "
                + this.tabuSize;
    }

    public double[] getVariableHeuristics() {
        return this.decorated.getVariableHeuristics();
    }

}
