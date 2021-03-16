/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2019 Artois University and CNRS
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

package org.sat4j.tools.counting;

import org.sat4j.specs.ISolver;
import org.sat4j.specs.IteratorInt;

/**
 * The AllVariablesSamplingSet considers as sampling set all the variables of
 * the formula.
 * 
 * @author Romain Wallon
 */
public final class AllVariablesSamplingSet implements SamplingSet {

    /**
     * The solver from which to select variables.
     */
    private final ISolver solver;

    /**
     * Creates a new AllVariablesSamplingSet.
     * 
     * @param solver
     *            The solver from which to select variables.
     */
    private AllVariablesSamplingSet(ISolver solver) {
        this.solver = solver;
    }

    /**
     * Creates a new AllVariablesSamplingSet.
     * 
     * @param solver
     *            The solver from which to select variables.
     * 
     * @return The created sampling set.
     */
    public static SamplingSet of(ISolver solver) {
        return new AllVariablesSamplingSet(solver);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.SamplingSet#nVars()
     */
    @Override
    public int nVars() {
        return solver.nVars();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.tools.counting.SamplingSet#variables()
     */
    @Override
    public IteratorInt variables() {
        return new IteratorInt() {

            int currentVariable = 1;

            @Override
            public int next() {
                return currentVariable++;
            }

            @Override
            public boolean hasNext() {
                return currentVariable <= solver.nVars();
            }

        };
    }

}
