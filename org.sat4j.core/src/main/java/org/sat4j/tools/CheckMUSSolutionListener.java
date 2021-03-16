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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.sat4j.annotations.Feature;
import org.sat4j.core.ASolverFactory;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

@Feature("solutionlistener")
public class CheckMUSSolutionListener implements SolutionFoundListener {

    private List<IVecInt> clauses;

    private String explain;

    private final ASolverFactory<? extends ISolver> factory;

    public CheckMUSSolutionListener(ASolverFactory<? extends ISolver> factory) {
        this.clauses = new ArrayList<IVecInt>();
        this.factory = factory;
    }

    public void addOriginalClause(IVecInt clause) {
        IVecInt newClause = new VecInt(clause.size());
        if (clauses == null) {
            this.clauses = new ArrayList<IVecInt>();
        }
        clause.copyTo(newClause);
        clauses.add(newClause);
    }

    /**
     * 
     * @param mus
     *            containing the clauses identifiers
     * @return true if mus is really minimal unsatisfiable.
     */
    public boolean checkThatItIsAMUS(IVecInt mus) {
        boolean result = false;

        ISolver solver = factory.defaultSolver();

        try {
            for (int i = 0; i < mus.size(); i++) {
                solver.addClause(clauses.get(mus.get(i) - 1));
            }

            result = !solver.isSatisfiable();

            if (!result) {
                explain = "The set of clauses in the MUS is SAT : "
                        + Arrays.toString(solver.model());
                return result;
            }

        } catch (ContradictionException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Trivial inconsistency", e);
            result = true;
        } catch (TimeoutException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Timeout when checking unsatisfiability", e);
        }

        try {
            for (int i = 0; i < mus.size(); i++) {
                solver = factory.defaultSolver();
                for (int j = 0; j < mus.size(); j++) {
                    if (j != i) {
                        solver.addClause(clauses.get(mus.get(j) - 1));
                    }
                }
                result = result && solver.isSatisfiable();
                if (!result) {
                    explain = "The subset of clauses in the MUS not containing clause "
                            + (i + 1) + " is SAT : "
                            + Arrays.toString(solver.model());
                    return result;
                }
            }
        } catch (ContradictionException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Trivial inconsistency", e);
            result = false;
        } catch (TimeoutException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Timeout when checking satisfiability", e);
        }

        return result;

    }

    public void onSolutionFound(int[] solution) {

    }

    public void onSolutionFound(IVecInt solution) {
        if (checkThatItIsAMUS(solution)) {
            System.out.println(solution + " is a MUS");
        } else {
            System.out.println(solution + " is not a MUS \n" + explain);
        }
    }

    public void onUnsatTermination() {
        // do nothing
    }
}
