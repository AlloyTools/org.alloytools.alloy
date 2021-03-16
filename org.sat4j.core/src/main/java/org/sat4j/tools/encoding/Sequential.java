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
 * Implementation of the sequential encoding for the at most k constraint.
 * 
 * For the cases "at most k", we can use the sequential encoding described in:
 * C. Sinz,
 * "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints", in
 * International Conference on Principles and Practices of Constraint
 * Programming , 2005
 * 
 * @author sroussel
 * @since 2.3.1
 * 
 */
public class Sequential extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * This encoding adds (n-1)*k variables (n is the number of variables in the
     * at most constraint and k is the degree of the constraint) and 2nk+n-3k-1
     * clauses.
     */
    @Override
    public IConstr addAtMost(ISolver solver, IVecInt literals, int k)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        final int n = literals.size();

        if (n == 1) {
            return group;
        }

        int s[][] = new int[n - 1][k];
        for (int j = 0; j < k; j++) {
            for (int i = 0; i < n - 1; i++) {
                s[i][j] = solver.nextFreeVarId(true);
            }
        }
        IVecInt clause = new VecInt();
        clause.push(-literals.get(0));
        clause.push(s[0][0]);
        group.add(solver.addClause(clause));
        clause.clear();
        for (int j = 1; j < k; j++) {
            clause.push(-s[0][j]);
            group.add(solver.addClause(clause));
            clause.clear();
        }
        clause.push(-literals.get(n - 1));
        clause.push(-s[n - 2][k - 1]);
        group.add(solver.addClause(clause));
        clause.clear();
        for (int i = 1; i < n - 1; i++) {
            clause.push(-literals.get(i));
            clause.push(s[i][0]);
            group.add(solver.addClause(clause));
            clause.clear();
            clause.push(-s[i - 1][0]);
            clause.push(s[i][0]);
            group.add(solver.addClause(clause));
            clause.clear();
            for (int j = 1; j < k; j++) {
                clause.push(-literals.get(i));
                clause.push(-s[i - 1][j - 1]);
                clause.push(s[i][j]);
                group.add(solver.addClause(clause));
                clause.clear();
                clause.push(-s[i - 1][j]);
                clause.push(s[i][j]);
                group.add(solver.addClause(clause));
                clause.clear();
            }
            clause.push(-literals.get(i));
            clause.push(-s[i - 1][k - 1]);
            group.add(solver.addClause(clause));
            clause.clear();
        }
        return group;
    }

    @Override
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        return addAtMost(solver, literals, 1);
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
