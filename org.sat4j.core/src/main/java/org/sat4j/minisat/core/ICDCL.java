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

import org.sat4j.specs.ILogAble;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.UnitPropagationListener;

/**
 * Abstraction for Conflict Driven Clause Learning Solver.
 * 
 * Allows to easily access the various options available to setup the solver.
 * 
 * @author daniel
 * 
 * @param <D>
 */
public interface ICDCL<D extends DataStructureFactory> extends ISolver,
        UnitPropagationListener, ActivityListener, Learner {

    /**
     * Change the internal representation of the constraints. Note that the
     * heuristics must be changed prior to calling that method.
     * 
     * @param dsf
     *            the internal factory
     */
    void setDataStructureFactory(D dsf);

    /**
     * 
     * @since 2.2
     * @deprecated renamed into setLearningStrategy()
     * @see #setLearningStrategy(LearningStrategy)
     */
    @Deprecated
    void setLearner(LearningStrategy<D> learner);

    /**
     * Allow to change the learning strategy, i.e. to decide which
     * clauses/constraints should be learned by the solver after conflict
     * analysis.
     * 
     * @since 2.3.3
     */
    void setLearningStrategy(LearningStrategy<D> strategy);

    void setSearchParams(SearchParams sp);

    SearchParams getSearchParams();

    SolverStats getStats();

    void setRestartStrategy(RestartStrategy restarter);

    RestartStrategy getRestartStrategy();

    /**
     * Setup the reason simplification strategy. By default, there is no reason
     * simplification. NOTE THAT REASON SIMPLIFICATION DOES NOT WORK WITH
     * SPECIFIC DATA STRUCTURE FOR HANDLING BOTH BINARY AND TERNARY CLAUSES.
     * 
     * @param simp
     *            a simplification type.
     * 
     */
    void setSimplifier(SimplificationType simp);

    /**
     * Setup the reason simplification strategy. By default, there is no reason
     * simplification. NOTE THAT REASON SIMPLIFICATION IS ONLY ALLOWED FOR WL
     * CLAUSAL data structures. USING REASON SIMPLIFICATION ON CB CLAUSES,
     * CARDINALITY CONSTRAINTS OR PB CONSTRAINTS MIGHT RESULT IN INCORRECT
     * RESULTS.
     * 
     * @param simp
     */
    void setSimplifier(ISimplifier simp);

    ISimplifier getSimplifier();

    /**
     * @param lcds
     * @since 2.1
     */
    void setLearnedConstraintsDeletionStrategy(
            LearnedConstraintsDeletionStrategy lcds);

    /**
     * 
     * @param timer
     *            when to apply constraints cleanup.
     * @param evaluation
     *            the strategy used to evaluate learned clauses.
     * @since 2.3.2
     */
    void setLearnedConstraintsDeletionStrategy(ConflictTimer timer,
            LearnedConstraintsEvaluationType evaluation);

    /**
     * 
     * @param evaluation
     *            the strategy used to evaluate learned clauses.
     * @since 2.3.2
     */
    void setLearnedConstraintsDeletionStrategy(
            LearnedConstraintsEvaluationType evaluation);

    IOrder getOrder();

    void setOrder(IOrder h);

    void setNeedToReduceDB(boolean needToReduceDB);

    void setLogger(ILogAble out);

    ILogAble getLogger();
}