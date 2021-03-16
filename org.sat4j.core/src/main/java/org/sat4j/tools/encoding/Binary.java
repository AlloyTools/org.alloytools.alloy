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
 * Binary encoding for the "at most one" and "at most k" cases.
 * 
 * For the case "at most one", we can use the binary encoding (also called
 * birwise encoding) first described in A. M. Frisch, T. J. Peugniez, A. J.
 * Dogget and P. Nightingale, "Solving Non-Boolean Satisfiability Problems With
 * Stochastic Local Search: A Comparison of Encodings" in Journal of Automated
 * Reasoning, vol. 35, n 1-3, 2005.
 * 
 * The approach is generalized for the "at most k" case in A. M. Frisch and P.
 * A. Giannaros, "SAT Encodings of the At-Most-k Constraint", in International
 * Workshop on Modelling and Reformulating Constraint Satisfaction Problems,
 * 2010
 * 
 * @author sroussel
 * @since 2.3.1
 */
public class Binary extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * p being the smaller integer greater than log_2(n), this encoding adds p
     * variables and n*p clauses.
     * 
     */
    @Override
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);

        final int n = literals.size();
        final int p = (int) Math.ceil(Math.log(n) / Math.log(2));
        final int k = (int) Math.pow(2, p) - n;

        IVecInt clause = new VecInt();
        String binary = "";

        if (p == 0) {
            return group;
        }

        int y[] = new int[p];
        for (int i = 0; i < p; i++) {
            y[i] = solver.nextFreeVarId(true);
        }

        for (int i = 0; i < k; i++) {
            binary = Integer.toBinaryString(i);
            while (binary.length() != p - 1) {
                binary = "0" + binary;
            }

            for (int j = 0; j < p - 1; j++) {
                clause.push(-literals.get(i));
                if (binary.charAt(j) == '0') {
                    clause.push(-y[j]);
                } else {
                    clause.push(y[j]);
                }
                group.add(solver.addClause(clause));
                clause.clear();

            }
        }

        for (int i = k; i < n; i++) {
            binary = Integer.toBinaryString(2 * k + i - k);
            while (binary.length() != p) {
                binary = "0" + binary;
            }
            for (int j = 0; j < p; j++) {
                clause.push(-literals.get(i));
                if (binary.charAt(j) == '0') {
                    clause.push(-y[j]);
                } else {
                    clause.push(y[j]);
                }
                group.add(solver.addClause(clause));
                clause.clear();
            }

        }

        return group;
    }

    @Override
    public IConstr addAtMost(ISolver solver, IVecInt literals, int k)
            throws ContradictionException {

        final int n = literals.size();
        final int p = (int) Math.ceil(Math.log(n) / Math.log(2));

        ConstrGroup group = new ConstrGroup(false);

        int[][] b = new int[k][p];

        for (int i = 0; i < k; i++) {
            for (int j = 0; j < p; j++) {
                b[i][j] = solver.nextFreeVarId(true);
            }
        }

        int[][] t = new int[k][n];

        for (int i = 0; i < k; i++) {
            for (int j = 0; j < n; j++) {
                t[i][j] = solver.nextFreeVarId(true);
            }
        }

        int max, min;
        IVecInt clause1 = new VecInt();
        IVecInt clause2 = new VecInt();
        String binary = "";
        for (int i = 0; i < n; i++) {
            max = Math.max(1, k - n + i + 1);
            min = Math.min(i + 1, k);
            clause1.push(-literals.get(i));

            binary = Integer.toBinaryString(i);
            while (binary.length() != p) {
                binary = "0" + binary;
            }

            for (int g = max - 1; g < min; g++) {
                clause1.push(t[g][i]);
                for (int j = 0; j < p; j++) {
                    clause2.push(-t[g][i]);
                    if (binary.charAt(j) == '0') {
                        clause2.push(-b[g][j]);
                    } else {
                        clause2.push(b[g][j]);
                    }
                    group.add(solver.addClause(clause2));
                    clause2.clear();
                }
            }
            group.add(solver.addClause(clause1));
            clause1.clear();
        }

        return group;
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
