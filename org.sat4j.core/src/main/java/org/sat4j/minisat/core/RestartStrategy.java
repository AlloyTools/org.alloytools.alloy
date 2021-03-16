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
package org.sat4j.minisat.core;

import java.io.Serializable;

import org.sat4j.annotations.Feature;
import org.sat4j.specs.Constr;

/**
 * Abstraction allowing to choose various restarts strategies.
 * 
 * @author leberre
 * 
 */
@Feature(value = "restarts", parent = "expert")
public interface RestartStrategy extends Serializable, ConflictTimer {

    /**
     * Hook method called just before the search starts.
     * 
     * @param params
     *            the user's search parameters.
     * @param stats
     *            some statistics about the search (number of conflicts,
     *            restarts, etc).
     * 
     */
    void init(SearchParams params, SolverStats stats);

    /**
     * Ask for the next restart in number of conflicts. Deprecated since 2.3.2
     * 
     * @return the delay in conflicts before the next restart.
     */
    @Deprecated
    long nextRestartNumberOfConflict();

    /**
     * Ask the strategy if the solver should restart.
     * 
     * @return true if the solver should restart, else false.
     */
    boolean shouldRestart();

    /**
     * Hook method called when a restart occurs (once the solver has backtracked
     * to top decision level).
     * 
     */
    void onRestart();

    /**
     * Called when the solver backjumps to the root level.
     * 
     * @since 2.3.2
     */
    void onBackjumpToRootLevel();

    /**
     * Callback method called when a new clause is learned by the solver, after
     * conflict analysis.
     * 
     * @param learned
     *            the new clause
     * @param trailLevel
     *            the number of literals assigned when the conflict occurred.
     * @since 2.3.3
     */
    void newLearnedClause(Constr learned, int trailLevel);
}
