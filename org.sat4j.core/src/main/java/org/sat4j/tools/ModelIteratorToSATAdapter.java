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

import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * This class allow to use the ModelIterator class as a solver.
 * 
 * @author lonca
 */
public class ModelIteratorToSATAdapter extends ModelIterator {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    private int[] lastModel = null;
    private final SolutionFoundListener sfl;

    public ModelIteratorToSATAdapter(ISolver solver, SolutionFoundListener sfl) {
        this(solver, Long.MAX_VALUE, sfl);
    }

    public ModelIteratorToSATAdapter(ISolver solver, long bound,
            SolutionFoundListener sfl) {
        super(solver, bound);
        this.sfl = sfl;
    }

    @Override
    public boolean isSatisfiable() throws TimeoutException {
        boolean isSat = false;
        while (super.isSatisfiable()) {
            isSat = true;
            lastModel = super.model();
            this.sfl.onSolutionFound(lastModel);
        }
        expireTimeout();
        return isSat;
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        boolean isSat = false;
        while (super.isSatisfiable(assumps)) {
            isSat = true;
            lastModel = super.model();
            this.sfl.onSolutionFound(lastModel);
        }
        expireTimeout();
        return isSat;
    }

    @Override
    public int[] model() {
        return this.lastModel;
    }

}
