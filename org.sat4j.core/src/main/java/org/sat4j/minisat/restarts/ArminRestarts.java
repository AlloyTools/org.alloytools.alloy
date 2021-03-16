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
import org.sat4j.minisat.core.RestartStrategy;
import org.sat4j.minisat.core.SearchParams;
import org.sat4j.minisat.core.SolverStats;
import org.sat4j.specs.Constr;

/**
 * Rapid restart strategy presented by Armin Biere during it's SAT 07 invited
 * talk.
 * 
 * @author leberre
 * 
 */
@Feature(value = "restarts", parent = "expert")
public final class ArminRestarts implements RestartStrategy {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private double inner, outer;
    private long conflicts;
    private SearchParams params;

    private long conflictcount = 0;

    public void init(SearchParams theParams, SolverStats stats) {
        this.params = theParams;
        this.inner = theParams.getInitConflictBound();
        this.outer = theParams.getInitConflictBound();
        this.conflicts = Math.round(this.inner);
    }

    public long nextRestartNumberOfConflict() {
        return this.conflicts;
    }

    public void onRestart() {
        if (this.inner >= this.outer) {
            this.outer *= this.params.getConflictBoundIncFactor();
            this.inner = this.params.getInitConflictBound();
        } else {
            this.inner *= this.params.getConflictBoundIncFactor();
        }
        this.conflicts = Math.round(this.inner);
        this.conflictcount = 0;
    }

    @Override
    public String toString() {
        return "Armin Biere (Picosat) restarts strategy";
    }

    public boolean shouldRestart() {
        return this.conflictcount >= this.conflicts;
    }

    public void onBackjumpToRootLevel() {
        this.conflictcount = 0;
    }

    public void reset() {
        this.conflictcount = 0;
    }

    public void newConflict() {
        this.conflictcount++;
    }

    public void newLearnedClause(Constr learned, int trailLevel) {
    }
}
