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

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Computes models with a minimal subset (with respect to set inclusion) of
 * negative literals. This is done be adding a clause containing the negation of
 * the negative literals appearing in the model found (which prevents any
 * interpretation containing that subset of negative literals to be a model of
 * the formula).
 * 
 * Computes only one model minimal for inclusion, since there is currently no
 * way to save the state of the solver.
 * 
 * @author leberre
 * 
 * @see org.sat4j.specs.ISolver#addClause(IVecInt)
 */
@Feature("solver")
public class Minimal4InclusionModel extends AbstractMinimalModel {

    private static final long serialVersionUID = 1L;

    private int[] prevfullmodel;

    /**
     * 
     * @param solver
     * @param p
     *            the set of literals on which the minimality for inclusion is
     *            computed.
     * @param modelListener
     *            an object to be notified when a new model is found.
     */
    public Minimal4InclusionModel(ISolver solver, IVecInt p,
            SolutionFoundListener modelListener) {
        super(solver, p, modelListener);
    }

    /**
     * 
     * @param solver
     * @param p
     *            the set of literals on which the minimality for inclusion is
     *            computed.
     */
    public Minimal4InclusionModel(ISolver solver, IVecInt p) {
        this(solver, p, SolutionFoundListener.VOID);
    }

    /**
     * @param solver
     */
    public Minimal4InclusionModel(ISolver solver) {
        this(solver, negativeLiterals(solver), SolutionFoundListener.VOID);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#model()
     */
    @Override
    public int[] model() {
        int[] prevmodel = null;
        IVecInt vec = new VecInt();
        IVecInt cube = new VecInt();
        IConstr prevConstr = null;
        try {
            do {
                prevfullmodel = super.modelWithInternalVariables();
                prevmodel = super.model();
                modelListener.onSolutionFound(prevmodel);
                vec.clear();
                cube.clear();
                assumps.copyTo(cube);
                for (int q : prevfullmodel) {
                    if (pLiterals.contains(q)) {
                        vec.push(-q);
                    } else if (pLiterals.contains(-q)) {
                        cube.push(q);
                    }
                }
                if (prevConstr != null) {
                    removeSubsumedConstr(prevConstr);
                }
                try {
                    prevConstr = addBlockingClause(vec);
                } catch (ContradictionException e) {
                    // added trivial unsat clauses
                    break;
                }
            } while (isSatisfiable(cube));
        } catch (TimeoutException e) {
            throw new IllegalStateException("Solver timed out");
        }
        return prevmodel;

    }

    @Override
    public int[] modelWithInternalVariables() {
        model();
        return prevfullmodel;
    }

    private IVecInt assumps = VecInt.EMPTY;

    @Override
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        this.assumps = assumps;
        return super.isSatisfiable(assumps);
    }
}
