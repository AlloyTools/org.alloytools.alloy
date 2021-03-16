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
 * 
 * Ladder encoding for the "at most one" and "exactly one" cases.
 * 
 * The ladder encoding described in: I. P. Gent and P. Nightingale,
 * "A new encoding for AllDifferent into SAT", in International Workshop on
 * Modeling and Reformulating Constraint Satisfaction Problems, 2004
 * 
 * @author sroussel
 * @since 2.3.1
 */
public class Ladder extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    @Override
    /**
     * If n is the number of variables in the constraint, 
     * this encoding adds n variables and 4n clauses 
     * (3n+1 size 2 clauses and n-1 size 3 clauses)
     */
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        final int n = literals.size() + 1;

        int xN = solver.nextFreeVarId(true);
        int y[] = new int[n - 1];

        for (int i = 0; i < n - 1; i++) {
            y[i] = solver.nextFreeVarId(true);
        }

        IVecInt clause = new VecInt();

        // Constraint \bigwedge_{i=1}{n-2} (\neg y_{i+1} \vee y_i)
        for (int i = 1; i <= n - 2; i++) {
            clause.push(-y[i]);
            clause.push(y[i - 1]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg y_{i-1} \vee y_i \vee x_i)
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-y[i - 2]);
            clause.push(y[i - 1]);
            clause.push(literals.get(i - 1));
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg x_i \vee y_{i-1)})
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-literals.get(i - 1));
            clause.push(y[i - 2]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg x_i \vee \neg y_i)
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-literals.get(i - 1));
            clause.push(-y[i - 1]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint y_1 \vee x_1
        clause.push(y[0]);
        clause.push(literals.get(0));
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint \neg y_1 \vee \neg x_1
        clause.push(-y[0]);
        clause.push(-literals.get(0));
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint \neg y_{n-1} \vee x_n
        clause.push(-y[n - 2]);
        clause.push(xN);
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint y_{n-1} \vee \neg x_n
        clause.push(y[n - 2]);
        clause.push(-xN);
        group.add(solver.addClause(clause));
        clause.clear();

        return group;
    }

    @Override
    /**
     * If n is the number of variables in the constraint, 
     * this encoding adds n-1 variables and 4(n-1) clauses 
     * (3n-2 size 2 clauses and n-2 size 3 clauses)
     */
    public IConstr addExactlyOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);
        final int n = literals.size();

        IVecInt clause = new VecInt();

        if (n == 1) {
            clause.push(literals.get(0));
            group.add(solver.addClause(clause));
            return group;
        }

        int y[] = new int[n - 1];

        for (int i = 0; i < n - 1; i++) {
            y[i] = solver.nextFreeVarId(true);
        }

        // Constraint \bigwedge_{i=1}{n-2} (\neg y_{i+1} \vee y_i)
        for (int i = 1; i <= n - 2; i++) {
            clause.push(-y[i]);
            clause.push(y[i - 1]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg y_{i-1} \vee y_i \vee x_i)
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-y[i - 2]);
            clause.push(y[i - 1]);
            clause.push(literals.get(i - 1));
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg x_i \vee y_{i-1)})
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-literals.get(i - 1));
            clause.push(y[i - 2]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint \bigwedge_{i=2}{n-1} (\neg x_i \vee \neg y_i)
        for (int i = 2; i <= n - 1; i++) {
            clause.push(-literals.get(i - 1));
            clause.push(-y[i - 1]);
            group.add(solver.addClause(clause));
            clause.clear();
        }

        // Constraint y_1 \vee x_1
        clause.push(y[0]);
        clause.push(literals.get(0));
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint \neg y_1 \vee \neg x_1
        clause.push(-y[0]);
        clause.push(-literals.get(0));
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint \neg y_{n-1} \vee x_n
        clause.push(-y[n - 2]);
        clause.push(literals.get(n - 1));
        group.add(solver.addClause(clause));
        clause.clear();

        // Constraint y_{n-1} \vee \neg x_n
        clause.push(y[n - 2]);
        clause.push(-literals.get(n - 1));
        group.add(solver.addClause(clause));
        clause.clear();

        return group;
    }
}
