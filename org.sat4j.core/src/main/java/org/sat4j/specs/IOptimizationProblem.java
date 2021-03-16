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

/**
 * Represents an optimization problem. The SAT solver will find suboptimal
 * solutions of the problem until no more solutions are available. The latest
 * solution found will be the optimal one.
 * 
 * Such kind of problem is supposed to be handled:
 * 
 * <pre>
 * boolean isSatisfiable = false;
 * 
 * IOptimizationProblem optproblem = (IOptimizationProblem) problem;
 * 
 * try {
 *     while (optproblem.admitABetterSolution()) {
 *         if (!isSatisfiable) {
 *             if (optproblem.nonOptimalMeansSatisfiable()) {
 *                 setExitCode(ExitCode.SATISFIABLE);
 *                 if (optproblem.hasNoObjectiveFunction()) {
 *                     return;
 *                 }
 *                 log(&quot;SATISFIABLE&quot;); //$NON-NLS-1$
 *             }
 *             isSatisfiable = true;
 *             log(&quot;OPTIMIZING...&quot;); //$NON-NLS-1$
 *         }
 *         log(&quot;Got one! Elapsed wall clock time (in seconds):&quot; //$NON-NLS-1$
 *                 + (System.currentTimeMillis() - getBeginTime()) / 1000.0);
 *         getLogWriter().println(
 *                 CURRENT_OPTIMUM_VALUE_PREFIX + optproblem.getObjectiveValue());
 *         optproblem.discardCurrentSolution();
 *     }
 *     if (isSatisfiable) {
 *         setExitCode(ExitCode.OPTIMUM_FOUND);
 *     } else {
 *         setExitCode(ExitCode.UNSATISFIABLE);
 *     }
 * } catch (ContradictionException ex) {
 *     assert isSatisfiable;
 *     setExitCode(ExitCode.OPTIMUM_FOUND);
 * }
 * </pre>
 * 
 * @author leberre
 * 
 */
public interface IOptimizationProblem extends IProblem {

    /**
     * Look for a solution of the optimization problem.
     * 
     * @return true if a better solution than current one can be found.
     * @throws TimeoutException
     *             if the solver cannot answer in reasonable time.
     * @see ISolver#setTimeout(int)
     */
    boolean admitABetterSolution() throws TimeoutException;

    /**
     * Look for a solution of the optimization problem when some literals are
     * satisfied.
     * 
     * @param assumps
     *            a set of literals in Dimacs format.
     * @return true if a better solution than current one can be found.
     * @throws TimeoutException
     *             if the solver cannot answer in reasonable time.
     * @see ISolver#setTimeout(int)
     * @since 2.1
     */
    boolean admitABetterSolution(IVecInt assumps) throws TimeoutException;

    /**
     * If the optimization problem has no objective function, then it is a
     * simple decision problem.
     * 
     * @return true if the problem is a decision problem, false if the problem
     *         is an optimization problem.
     */
    boolean hasNoObjectiveFunction();

    /**
     * A suboptimal solution has different meaning depending of the optimization
     * problem considered.
     * 
     * For instance, in the case of MAXSAT, a suboptimal solution does not mean
     * that the problem is satisfiable, while in pseudo boolean optimization, it
     * is true.
     * 
     * @return true if founding a suboptimal solution means that the problem is
     *         satisfiable.
     */
    boolean nonOptimalMeansSatisfiable();

    /**
     * Compute the value of the objective function for the current solution. A
     * call to that method only makes sense if hasNoObjectiveFunction()==false.
     * 
     * DO NOT CALL THAT METHOD THAT WILL BE CALLED AUTOMATICALLY. USE
     * getObjectiveValue() instead!
     * 
     * @return the value of the objective function.
     * @see #getObjectiveValue()
     */
    @Deprecated
    Number calculateObjective();

    /**
     * Read only access to the value of the objective function for the current
     * solution.
     * 
     * @return the value of the objective function for the current solution.
     * @since 2.1
     */
    Number getObjectiveValue();

    /**
     * Force the value of the objective function.
     * 
     * This is especially useful to iterate over optimal solutions.
     * 
     * @throws ContradictionException
     * @since 2.1
     */
    void forceObjectiveValueTo(Number forcedValue)
            throws ContradictionException;

    /**
     * Discard the current solution in the optimization problem.
     * 
     * THE NAME WAS NOT NICE. STILL AVAILABLE TO AVOID BREAKING THE API. PLEASE
     * USE THE LONGER discardCurrentSolution() instead.
     * 
     * @throws ContradictionException
     *             if a trivial inconsistency is detected.
     * @see #discardCurrentSolution()
     */
    @Deprecated
    void discard() throws ContradictionException;

    /**
     * Discard the current solution in the optimization problem.
     * 
     * @throws ContradictionException
     *             if a trivial inconsistency is detected.
     * @since 2.1
     */
    void discardCurrentSolution() throws ContradictionException;

    /**
     * Allows to check afterwards if the solution provided by the solver is
     * optimal or not.
     * 
     * @return
     */
    boolean isOptimal();

    /**
     * Allow to set a specific timeout when the solver is in optimization mode.
     * The solver internal timeout will be set to that value once it has found a
     * solution. That way, the original timeout of the solver may be reduced if
     * the solver finds quickly a solution, or increased if the solver finds
     * regularly new solutions (thus giving more time to the solver each time).
     * 
     * @since 2.3.3
     */
    void setTimeoutForFindingBetterSolution(int seconds);
}
