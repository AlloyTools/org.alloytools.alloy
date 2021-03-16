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
 * Computes models with a minimal number (with respect to cardinality) of
 * negative literals. This is done be adding a constraint on the number of
 * negative literals each time a model if found (the number of negative literals
 * occuring in the model minus one).
 * 
 * @author leberre
 * @see org.sat4j.specs.ISolver#addAtMost(IVecInt, int)
 */
@Feature("solver")
public class Minimal4CardinalityModel extends AbstractMinimalModel {

    private static final long serialVersionUID = 1L;

    private int[] prevfullmodel;

    /**
     * @param solver
     */
    public Minimal4CardinalityModel(ISolver solver) {
        super(solver);
    }

    public Minimal4CardinalityModel(ISolver solver, IVecInt p,
            SolutionFoundListener modelListener) {
        super(solver, p, modelListener);
    }

    public Minimal4CardinalityModel(ISolver solver, IVecInt p) {
        super(solver, p);
    }

    public Minimal4CardinalityModel(ISolver solver,
            SolutionFoundListener modelListener) {
        super(solver, modelListener);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.ISolver#model()
     */
    @Override
    public int[] model() {
        int[] prevmodel = null;
        IConstr lastOne = null;
        IVecInt literals = new VecInt(pLiterals.size());
        for (int p : pLiterals) {
            literals.push(p);
        }
        try {
            do {
                prevfullmodel = super.modelWithInternalVariables();
                prevmodel = super.model();
                int counter = 0;
                for (int q : prevfullmodel) {
                    if (pLiterals.contains(q)) {
                        counter++;
                    }
                }
                lastOne = addAtMost(literals, counter - 1);
            } while (isSatisfiable());
        } catch (TimeoutException e) {
            throw new IllegalStateException("Solver timed out"); //$NON-NLS-1$
        } catch (ContradictionException e) {
            // added trivial unsat clauses
        }
        if (lastOne != null) {
            removeConstr(lastOne);
        }
        return prevmodel;
    }

    @Override
    public int[] modelWithInternalVariables() {
        model();
        return prevfullmodel;
    }
}
