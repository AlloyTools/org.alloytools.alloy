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

/**
 * The responsibility of that class is to choose the phase (positive or
 * negative) of the variable that was selected by the IOrder.
 * 
 * @author leberre
 * 
 */
@Feature(value = "phaseheuristics", parent = "expert")
public interface IPhaseSelectionStrategy extends Serializable {

    /**
     * To be called when the activity of a literal changed.
     * 
     * @param p
     *            a literal. The associated variable will be updated.
     */
    void updateVar(int p);

    /**
     * that method has the responsibility to initialize all arrays in the
     * heuristics.
     * 
     * @param nlength
     *            the number of variables managed by the heuristics.
     */
    void init(int nlength);

    /**
     * initialize the phase of a given variable to the given value. That method
     * is suppose to be called AFTER init(int).
     * 
     * @param var
     *            a variable
     * @param p
     *            it's initial phase
     */
    void init(int var, int p);

    /**
     * indicate that a literal has been satisfied.
     * 
     * @param p
     */
    void assignLiteral(int p);

    /**
     * selects the phase of the variable according to a phase selection
     * strategy.
     * 
     * @param var
     *            a variable chosen by the heuristics
     * @return either var or not var, depending of the selection strategy.
     * 
     */
    int select(int var);

    /**
     * Allow to perform a specific action when a literal of the current decision
     * level is updated. That method is called after {@link #updateVar(int)}.
     * 
     * @param q
     *            a literal
     */
    void updateVarAtDecisionLevel(int q);
}
