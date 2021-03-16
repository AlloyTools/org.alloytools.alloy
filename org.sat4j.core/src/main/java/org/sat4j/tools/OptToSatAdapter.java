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
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

@Feature("solver")
public class OptToSatAdapter extends SolverDecorator<ISolver> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final IOptimizationProblem problem;

    private final IVecInt assumps = new VecInt();

    private long begin;

    private final SolutionFoundListener sfl;

    public OptToSatAdapter(IOptimizationProblem problem) {
        this(problem, SolutionFoundListener.VOID);
    }

    public OptToSatAdapter(IOptimizationProblem problem,
            SolutionFoundListener sfl) {
        super((ISolver) problem);
        this.problem = problem;
        this.sfl = sfl;
    }

    @Override
    public boolean isSatisfiable() throws TimeoutException {
        return isSatisfiable(VecInt.EMPTY);
    }

    @Override
    public boolean isSatisfiable(boolean global) throws TimeoutException {
        return isSatisfiable();
    }

    @Override
    public boolean isSatisfiable(IVecInt myAssumps, boolean global)
            throws TimeoutException {
        return isSatisfiable(myAssumps);
    }

    @Override
    public boolean isSatisfiable(IVecInt myAssumps) throws TimeoutException {
        this.assumps.clear();
        myAssumps.copyTo(this.assumps);
        this.begin = System.currentTimeMillis();
        if (this.problem.hasNoObjectiveFunction()) {
            return this.problem.isSatisfiable(myAssumps);
        }
        if (!this.problem.admitABetterSolution(myAssumps)) {
            return false;
        }
        try {
            do {
                sfl.onSolutionFound(this.problem.model());
                this.problem.discardCurrentSolution();
                if (isVerbose()) {
                    System.out.println(getLogPrefix()
                            + "Current objective function value: "
                            + this.problem.getObjectiveValue() + "("
                            + (System.currentTimeMillis() - this.begin) / 1000.0
                            + "s)");
                }
            } while (this.problem.admitABetterSolution(myAssumps));
            expireTimeout();
            sfl.onUnsatTermination();
        } catch (TimeoutException e) {
            if (isVerbose()) {
                System.out.println(getLogPrefix() + "Solver timed out after "
                        + (System.currentTimeMillis() - this.begin) / 1000.0
                        + "s)");
            }
        } catch (ContradictionException ce) {
            expireTimeout();
            sfl.onUnsatTermination();
        }
        return true;
    }

    @Override
    public int[] model() {
        return this.problem.model();
    }

    @Override
    public boolean model(int var) {
        return this.problem.model(var);
    }

    @Override
    public int[] modelWithInternalVariables() {
        return decorated().modelWithInternalVariables();
    }

    @Override
    public int[] findModel() throws TimeoutException {
        if (isSatisfiable()) {
            return model();
        }
        return null;
    }

    @Override
    public int[] findModel(IVecInt assumps) throws TimeoutException {
        if (isSatisfiable(assumps)) {
            return model();
        }
        return null;
    }

    @Override
    public String toString(String prefix) {
        return prefix + "Optimization to SAT adapter\n"
                + super.toString(prefix);
    }

    /**
     * Allow to easily check is the solution returned by isSatisfiable is
     * optimal or not.
     * 
     * @return true is the solution found is indeed optimal.
     */
    public boolean isOptimal() {
        return this.problem.isOptimal();
    }
}
