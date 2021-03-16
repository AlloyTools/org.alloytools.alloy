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

package org.sat4j.tools.encoding;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * Commander encoding for "at most one" and "at most k" cases.
 * 
 * The case "at most one" is introduced in W. Klieber and G. Kwon
 * "Efficient CNF encoding for selecting 1 from N objects" in Fourth Workshop on
 * Constraints in Formal Verification, 2007.
 * 
 * The generalization to the "at most k" case is described in A. M. Frisch and P
 * . A. Giannaros, "SAT Encodings of the At-Most-k Constraint", in International
 * Workshop on Modelling and Reformulating Constraint Satisfaction Problems,
 * 2010
 * 
 * @author sroussel
 * @since 2.3.1
 */
public class Commander extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * In this encoding, variables are partitioned in groups. Kwon and Klieber
     * claim that the fewest clauses are produced when the size of the groups is
     * 3, thus leading to 3.5 clauses and introducing n/2 variables.
     */
    @Override
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {

        return addAtMostOne(solver, literals, 3);
    }

    private IConstr addAtMostOne(ISolver solver, IVecInt literals, int groupSize)
            throws ContradictionException {

        ConstrGroup constrGroup = new ConstrGroup(false);

        IVecInt clause = new VecInt();
        IVecInt clause1 = new VecInt();

        final int n = literals.size();

        int nbGroup = (int) Math.ceil((double) literals.size()
                / (double) groupSize);

        if (nbGroup == 1) {
            for (int i = 0; i < literals.size() - 1; i++) {
                for (int j = i + 1; j < literals.size(); j++) {
                    clause.push(-literals.get(i));
                    clause.push(-literals.get(j));
                    constrGroup.add(solver.addClause(clause));
                    clause.clear();
                }
            }
            return constrGroup;
        }

        int[] c = new int[nbGroup];

        for (int i = 0; i < nbGroup; i++) {
            c[i] = solver.nextFreeVarId(true);
        }

        int nbVarLastGroup = n - (nbGroup - 1) * groupSize;

        // Encoding <=1 for each group of groupLitterals
        for (int i = 0; i < nbGroup; i++) {
            int size = 0;
            if (i == nbGroup - 1) {
                size = nbVarLastGroup;
            } else {
                size = groupSize;
            }
            // Encoding <=1 for each group of groupLitterals
            for (int j = 0; j < size - 1; j++) {
                for (int k = j + 1; k < size; k++) {
                    clause.push(-literals.get(i * groupSize + j));
                    clause.push(-literals.get(i * groupSize + k));
                    constrGroup.add(solver.addClause(clause));
                    clause.clear();
                }
            }

            // If a commander variable is true then some variable in its
            // corresponding group must be true (clause1)
            // If a commander variable is false then no variable in its group
            // can be true (clause)
            clause1.push(-c[i]);
            for (int j = 0; j < size; j++) {
                clause1.push(literals.get(i * groupSize + j));
                clause.push(c[i]);
                clause.push(-literals.get(i * groupSize + j));
                constrGroup.add(solver.addClause(clause));
                clause.clear();
            }
            constrGroup.add(solver.addClause(clause1));
            clause1.clear();
        }

        // encode <=1 on commander variables

        constrGroup.add(addAtMostOne(solver, new VecInt(c), groupSize));
        return constrGroup;
    }

    @Override
    public IConstr addExactlyOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);

        group.add(addAtLeastOne(solver, literals));
        group.add(addAtMostOne(solver, literals));

        return group;
    }

    @Override
    public IConstr addExactly(ISolver solver, IVecInt literals, int degree)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);

        group.add(addAtLeast(solver, literals, degree));
        group.add(addAtMost(solver, literals, degree));

        return group;
    }

}
