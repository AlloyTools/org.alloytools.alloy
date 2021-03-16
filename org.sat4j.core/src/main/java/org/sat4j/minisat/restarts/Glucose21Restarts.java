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
package org.sat4j.minisat.restarts;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.CircularBuffer;
import org.sat4j.minisat.core.RestartStrategy;
import org.sat4j.minisat.core.SearchParams;
import org.sat4j.minisat.core.SolverStats;
import org.sat4j.specs.Constr;

/**
 * Dynamic restart strategy of Glucose 2.1 as presented in Refining restarts
 * strategies for SAT and UNSAT formulae. Gilles Audemard and Laurent Simon, in
 * CP'2012.
 * 
 * @author leberre
 * 
 */
@Feature(value = "restarts", parent = "expert")
public class Glucose21Restarts implements RestartStrategy {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final CircularBuffer bufferLBD = new CircularBuffer(50);

    private final CircularBuffer bufferTrail = new CircularBuffer(5000);

    private long sumOfAllLBD = 0;

    private SolverStats stats;

    public void reset() {
        sumOfAllLBD = 0;
        bufferLBD.clear();
        bufferTrail.clear();
    }

    public void newConflict() {

    }

    public void newLearnedClause(Constr learned, int trailLevel) {
        // on conflict
        int lbd = (int) learned.getActivity();
        bufferLBD.push(lbd);
        sumOfAllLBD += lbd;
        bufferTrail.push(trailLevel);
        // was
        // ... trailLevel > 1.4 * bufferTrail.average()
        // uses now only integers to avoid rounding issues
        if (stats.getConflicts() > 10000 && bufferTrail.isFull()
                && trailLevel * 5L > 7L * bufferTrail.average()) {
            bufferLBD.clear();
        }
    }

    public void init(SearchParams params, SolverStats stats) {
        this.stats = stats;
        reset();
    }

    public long nextRestartNumberOfConflict() {
        return 0;
    }

    public boolean shouldRestart() {
        // was
        // ... && bufferLBD.average() * 0.8 > sumOfAllLBD / stats.conflicts
        // uses now only integers to avoid rounding issues
        return bufferLBD.isFull() && bufferLBD.average() * stats.getConflicts()
                * 4L > sumOfAllLBD * 5L;
    }

    public void onRestart() {
        bufferLBD.clear();
    }

    public void onBackjumpToRootLevel() {
    }

    @Override
    public String toString() {
        return "Glucose 2.1 dynamic restart strategy";
    }
}
