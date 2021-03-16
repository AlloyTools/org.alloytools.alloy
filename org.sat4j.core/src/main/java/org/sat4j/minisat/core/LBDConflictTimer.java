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

/**
 * Mimics the checks found in Glucose.
 * 
 * @author daniel
 * 
 */
final class GlucoseConflictTimer extends ConflictTimerAdapter {
    private static final long serialVersionUID = 1L;
    private int nbconflict = 0;
    private static final int MAX_CLAUSE = 5000;
    private static final int INC_CLAUSE = 1000;
    private int nextbound = MAX_CLAUSE;

    GlucoseConflictTimer(Solver<? extends DataStructureFactory> solver,
            int bound) {
        super(solver, bound);
    }

    @Override
    public void run() {
        this.nbconflict += bound();
        if (this.nbconflict >= this.nextbound) {
            this.nextbound += INC_CLAUSE;
            this.nbconflict = 0;
            getSolver().setNeedToReduceDB(true);
        }
    }

    @Override
    public void reset() {
        super.reset();
        this.nextbound = MAX_CLAUSE;
        if (this.nbconflict >= this.nextbound) {
            this.nbconflict = 0;
            getSolver().setNeedToReduceDB(true);
        }
    }

    @Override
    public String toString() {
        return "check every " + bound()
                + " if the learned constraints reach increasing bounds: "
                + MAX_CLAUSE + " step " + INC_CLAUSE;
    }

}