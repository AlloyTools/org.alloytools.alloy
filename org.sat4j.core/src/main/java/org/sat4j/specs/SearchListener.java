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
package org.sat4j.specs;

import java.io.Serializable;

import org.sat4j.annotations.Feature;

/**
 * Interface to the solver main steps. Useful for integrating search
 * visualization or debugging.
 * 
 * (that class moved from org.sat4j.minisat.core in earlier version of SAT4J).
 * 
 * @author daniel
 * @since 2.1
 */
@Feature("searchlistener")
public interface SearchListener<S extends ISolverService>
        extends UnitClauseConsumer, Serializable {

    /**
     * Provide access to the solver's controllable interface.
     * 
     * @param solverService
     *            a way to safely control the solver.
     * @since 2.3.2
     */
    void init(S solverService);

    /**
     * decision variable
     * 
     * @param p
     */
    void assuming(int p);

    /**
     * Unit propagation
     * 
     * @param p
     */
    void propagating(int p);

    /**
     * Fixes the truth value of a variable before propagating it. For all calls
     * to enqueueing(p,_) there should be a call to propagating(p) unless a
     * conflict is found.
     * 
     * @param p
     * @param reason
     *            TODO
     */
    void enqueueing(int p, IConstr reason);

    /**
     * backtrack on a decision variable
     * 
     * @param p
     */
    void backtracking(int p);

    /**
     * adding forced variable (conflict driven assignment)
     */
    void adding(int p);

    /**
     * learning a new clause
     * 
     * @param c
     */
    void learn(IConstr c);

    /**
     * delete a clause
     */
    void delete(IConstr c);

    /**
     * a conflict has been found.
     * 
     * @param confl
     *            TODO
     * @param dlevel
     *            TODO
     * @param trailLevel
     *            TODO
     * 
     */
    void conflictFound(IConstr confl, int dlevel, int trailLevel);

    /**
     * a conflict has been found while propagating values.
     * 
     * @param p
     *            the conflicting value.
     */
    void conflictFound(int p);

    /**
     * a solution is found.
     * 
     * @param model
     *            the model found
     * @param lazyModel
     *            TODO
     * 
     */
    void solutionFound(int[] model, RandomAccessModel lazyModel);

    /**
     * starts a propagation
     */
    void beginLoop();

    /**
     * Start the search.
     * 
     */
    void start();

    /**
     * End the search.
     * 
     * @param result
     *            the result of the search.
     */
    void end(Lbool result);

    /**
     * The solver restarts the search.
     */
    void restarting();

    /**
     * The solver is asked to backjump to a given decision level.
     * 
     * @param backjumpLevel
     */
    void backjump(int backjumpLevel);

    /**
     * The solver is going to delete some learned clauses.
     */
    void cleaning();
}
