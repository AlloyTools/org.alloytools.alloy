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
 * This solver decorator allows to detect whether or not the set of constraints
 * available in the solver has only one solution or not.
 * 
 * NOTE THAT THIS DECORATOR CANNOT BE USED WITH SOLVERS USING SPECIFIC DATA
 * STRUCTURES FOR BINARY OR TERNARY CLAUSES!
 * 
 * <code>
 SingleSolutionDetector problem = 
 new SingleSolutionDetector(SolverFactory.newMiniSAT());
 // feed problem/solver as usual

 if (problem.isSatisfiable()) {
 if (problem.hasASingleSolution()) {
 // great, the instance has a unique solution
 int [] uniquesolution = problem.getModel();
 } else {
 // too bad, got more than one
 }
 }
 *  </code>
 * 
 * @author leberre
 * 
 */
@Feature("solver")
public class SingleSolutionDetector extends SolverDecorator<ISolver> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public SingleSolutionDetector(ISolver solver) {
        super(solver);
    }

    /**
     * Please use that method only after a positive answer from isSatisfiable()
     * (else a runtime exception will be launched).
     * 
     * NOTE THAT THIS FUNCTION SHOULD NOT ONLY BE USED ONCE THE FINAL SOLUTION
     * IS FOUND, SINCE THE METHOD ADDS CONSTRAINTS INTO THE SOLVER THAT MAY NOT
     * BE REMOVED UNDER CERTAIN CONDITIONS (UNIT CONSTRAINTS LEARNT FOR
     * INSTANCE). THAT ISSUE WILL BE RESOLVED ONCE REMOVECONSTR WILL WORK
     * PROPERLY.
     * 
     * @return true iff there is only one way to satisfy all the constraints in
     *         the solver.
     * @throws TimeoutException
     * @see ISolver#removeConstr(IConstr)
     */
    public boolean hasASingleSolution() throws TimeoutException {
        return hasASingleSolution(new VecInt());
    }

    /**
     * Please use that method only after a positive answer from
     * isSatisfiable(assumptions) (else a runtime exception will be launched).
     * 
     * @param assumptions
     *            a set of literals (dimacs numbering) that must be satisfied.
     * @return true iff there is only one way to satisfy all the constraints in
     *         the solver using the provided set of assumptions.
     * @throws TimeoutException
     */
    public boolean hasASingleSolution(IVecInt assumptions)
            throws TimeoutException {
        int[] firstmodel = model();
        assert firstmodel != null;
        IVecInt clause = new VecInt(firstmodel.length);
        for (int q : firstmodel) {
            clause.push(-q);
        }
        boolean result = false;
        try {
            IConstr added = addClause(clause);
            result = !isSatisfiable(assumptions);
            removeConstr(added);
        } catch (ContradictionException e) {
            result = true;
        }
        return result;
    }
}
