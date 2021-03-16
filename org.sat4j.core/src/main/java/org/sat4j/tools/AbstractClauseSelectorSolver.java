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
package org.sat4j.tools;

import java.util.Collection;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;

public abstract class AbstractClauseSelectorSolver<T extends ISolver> extends
        SolverDecorator<T> {

    private static final long serialVersionUID = 1L;
    private int lastCreatedVar;
    private boolean pooledVarId = false;

    private interface SelectorState {

        boolean isSatisfiable(boolean global) throws TimeoutException;

        boolean isSatisfiable() throws TimeoutException;

        boolean isSatisfiable(IVecInt assumps) throws TimeoutException;

        boolean isSatisfiable(IVecInt assumps, boolean global)
                throws TimeoutException;

    }

    private final SelectorState external = new SelectorState() {

        private IVecInt getNegatedSelectors() {
            IVecInt assumps = new VecInt();
            for (int var : getAddedVars()) {
                assumps.push(-var);
            }
            return assumps;
        }

        public boolean isSatisfiable(boolean global) throws TimeoutException {
            return decorated().isSatisfiable(getNegatedSelectors(), global);
        }

        public boolean isSatisfiable(IVecInt assumps, boolean global)
                throws TimeoutException {
            IVecInt all = getNegatedSelectors();
            assumps.copyTo(all);
            return decorated().isSatisfiable(all, global);
        }

        public boolean isSatisfiable() throws TimeoutException {
            return decorated().isSatisfiable(getNegatedSelectors());
        }

        public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
            IVecInt all = getNegatedSelectors();
            assumps.copyTo(all);
            return decorated().isSatisfiable(all);
        }

    };

    private final SelectorState internal = new SelectorState() {

        public boolean isSatisfiable(boolean global) throws TimeoutException {
            return decorated().isSatisfiable(global);
        }

        public boolean isSatisfiable() throws TimeoutException {
            return decorated().isSatisfiable();
        }

        public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
            return decorated().isSatisfiable(assumps);
        }

        public boolean isSatisfiable(IVecInt assumps, boolean global)
                throws TimeoutException {
            return decorated().isSatisfiable(assumps, global);
        }
    };

    private SelectorState selectedState = external;

    public AbstractClauseSelectorSolver(T solver) {
        super(solver);
    }

    public abstract Collection<Integer> getAddedVars();

    /**
     * 
     * @param literals
     * @return
     * @since 2.1
     */
    protected int createNewVar(IVecInt literals) {
        for (IteratorInt it = literals.iterator(); it.hasNext();) {
            if (Math.abs(it.next()) > nextFreeVarId(false)) {
                throw new IllegalStateException(
                        "Please call newVar(int) before adding constraints!!!");
            }
        }
        if (this.pooledVarId) {
            this.pooledVarId = false;
            return this.lastCreatedVar;
        }
        this.lastCreatedVar = nextFreeVarId(true);
        return this.lastCreatedVar;
    }

    protected void discardLastestVar() {
        this.pooledVarId = true;
    }

    @Override
    public boolean isSatisfiable(boolean global) throws TimeoutException {
        return selectedState.isSatisfiable(global);
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps, boolean global)
            throws TimeoutException {
        return selectedState.isSatisfiable(assumps, global);
    }

    @Override
    public boolean isSatisfiable() throws TimeoutException {
        return selectedState.isSatisfiable();
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        return selectedState.isSatisfiable(assumps);
    }

    /**
     * In the internal state, the solver will allow the selector variables to be
     * satisfied. As such, the solver will answer "true" to isSatisfiable() on
     * an UNSAT problem. it is the responsibility of the user to take into
     * account the meaning of the selector variables.
     */
    public void internalState() {
        this.selectedState = internal;
    }

    /**
     * In external state, the solver will prevent the selector variables to be
     * satisfied. As a consequence, from an external point of view, an UNSAT
     * problem will answer "false" to isSatisfiable().
     */

    public void externalState() {
        this.selectedState = external;
    }
}
