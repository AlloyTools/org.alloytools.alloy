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

import java.io.PrintWriter;

/**
 * Access to the information related to a given problem instance.
 * 
 * @author leberre
 */
public interface IProblem extends RandomAccessModel {
    /**
     * Provide a model (if any) for a satisfiable formula. That method should be
     * called AFTER isSatisfiable() or isSatisfiable(IVecInt) if the formula is
     * satisfiable. Else an exception UnsupportedOperationException is launched.
     * 
     * @return a model of the formula as an array of literals to satisfy.
     * @see #isSatisfiable()
     * @see #isSatisfiable(IVecInt)
     */
    int[] model();

    /**
     * Provide a prime implicant, i.e. a set of literal that is sufficient to
     * satisfy all constraints of the problem.
     * 
     * 
     * @return a prime implicant of the formula as an array of literal, Dimacs
     *         format.
     * @since 2.3
     */
    int[] primeImplicant();

    /**
     * Check if a given literal is part of the prime implicant computed by the
     * {@link #primeImplicant()} method.
     * 
     * @param p
     *            a literal in Dimacs format
     * @return true iff p belongs to {@link #primeImplicant()}
     */
    boolean primeImplicant(int p);

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver.
     * 
     * @return true if the set of constraints is satisfiable, else false.
     */
    boolean isSatisfiable() throws TimeoutException;

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver.
     * 
     * @param assumps
     *            a set of literals (represented by usual non null integers in
     *            Dimacs format).
     * @param globalTimeout
     *            whether that call is part of a global process (i.e.
     *            optimization) or not. if (global), the timeout will not be
     *            reset between each call.
     * @return true if the set of constraints is satisfiable when literals are
     *         satisfied, else false.
     */
    boolean isSatisfiable(IVecInt assumps, boolean globalTimeout)
            throws TimeoutException;

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver.
     * 
     * @param globalTimeout
     *            whether that call is part of a global process (i.e.
     *            optimization) or not. if (global), the timeout will not be
     *            reset between each call.
     * @return true if the set of constraints is satisfiable, else false.
     */
    boolean isSatisfiable(boolean globalTimeout) throws TimeoutException;

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver.
     * 
     * @param assumps
     *            a set of literals (represented by usual non null integers in
     *            Dimacs format).
     * @return true if the set of constraints is satisfiable when literals are
     *         satisfied, else false.
     */
    boolean isSatisfiable(IVecInt assumps) throws TimeoutException;

    /**
     * Look for a model satisfying all the clauses available in the problem. It
     * is an alternative to isSatisfiable() and model() methods, as shown in the
     * pseudo-code: <code>
     if (isSatisfiable()) {
     return model();
     }
     return null; 
     </code>
     * 
     * @return a model of the formula as an array of literals to satisfy, or
     *         <code>null</code> if no model is found
     * @throws TimeoutException
     *             if a model cannot be found within the given timeout.
     * @since 1.7
     */
    int[] findModel() throws TimeoutException;

    /**
     * Look for a model satisfying all the clauses available in the problem. It
     * is an alternative to isSatisfiable(IVecInt) and model() methods, as shown
     * in the pseudo-code: <code>
     if (isSatisfiable(assumpt)) {
     return model();
     }
     return null; 
     </code>
     * 
     * @return a model of the formula as an array of literals to satisfy, or
     *         <code>null</code> if no model is found
     * @throws TimeoutException
     *             if a model cannot be found within the given timeout.
     * @since 1.7
     */
    int[] findModel(IVecInt assumps) throws TimeoutException;

    /**
     * To know the number of constraints currently available in the solver.
     * (without taking into account learned constraints).
     * 
     * @return the number of constraints added to the solver
     */
    int nConstraints();

    /**
     * Declare <code>howmany</code> variables in the problem (and thus in the
     * vocabulary), that will be represented using the Dimacs format by integers
     * ranging from 1 to howmany. That feature allows encodings to create
     * additional variables with identifier starting at howmany+1.
     * 
     * @param howmany
     *            number of variables to create
     * @return the total number of variables available in the solver (the
     *         highest variable number)
     * @see #nVars()
     */
    int newVar(int howmany);

    /**
     * To know the number of variables used in the solver as declared by
     * newVar()
     * 
     * In case the method newVar() has not been used, the method returns the
     * number of variables used in the solver.
     * 
     * @return the number of variables created using newVar().
     * @see #newVar(int)
     */
    int nVars();

    /**
     * To print additional informations regarding the problem.
     * 
     * @param out
     *            the place to print the information
     * @param prefix
     *            the prefix to put in front of each line
     * 
     */
    @Deprecated
    void printInfos(PrintWriter out, String prefix);

    /**
     * To print additional informations regarding the problem.
     * 
     * @param out
     *            the place to print the information
     * @since 2.3.3
     * 
     */
    void printInfos(PrintWriter out);

    /**
     * Get access to the decisions taken by the solver.
     * 
     * @return a set of Dimacs variables on which the solver had to decide to
     *         find the current model.
     * @since 3.0.0
     */
    int[] decisions();
}
