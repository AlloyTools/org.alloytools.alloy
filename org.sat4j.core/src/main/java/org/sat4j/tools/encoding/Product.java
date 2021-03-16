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

import java.util.ArrayList;
import java.util.HashMap;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * Implementation of product encoding for at most one and at most k constraints.
 * 
 * The encoding for "at most one" constraints was introduced by J. Chen in
 * "A New SAT Encoding for the At-Most-One Constraint" in Proceedings of the
 * Tenth International Workshop of Constraint Modeling and Reformulation, 2010
 * For the generalization to "at most k" constraint, we use the encoding
 * introduced in A. M. Frisch and P . A. Giannaros,
 * "SAT Encodings of the At-Most-k Constraint", in International Workshop on
 * Modelling and Reformulating Constraint Satisfaction Problems, 2010
 * 
 * @author sroussel
 * @since 2.3.1
 * 
 */
public class Product extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public IConstr addAtMostNonOpt(ISolver solver, IVecInt literals, int k)
            throws ContradictionException {

        ConstrGroup group = new ConstrGroup(false);

        IVecInt clause = new VecInt();

        final int n = literals.size();

        if (k > n) {
            return group;
        }
        if (n == k + 1) {
            for (int i = 0; i < n; i++) {
                clause.push(-literals.get(i));
            }
            group.add(solver.addClause(clause));
            clause.clear();
            return group;
        }
        if (n < 7) {
            Binomial binomial = new Binomial();

            return binomial.addAtMost(solver, literals, k);
        }

        final int p = (int) Math.ceil(Math.pow(n, 1 / (double) (k + 1)));

        int[][] a = new int[n][k + 1];
        int[] result;

        result = decompositionBase10VersBaseP(0, p, k + 1);
        a[0] = result;
        ArrayList<Integer> dejaPris = new ArrayList<Integer>();
        dejaPris.add(0);
        int tmp = 1;
        for (int i = 1; i <= k + 1; i++) {
            a[i] = decompositionBase10VersBaseP(tmp, p, k + 1);
            dejaPris.add(tmp);
            tmp = tmp * p;
        }
        tmp = 2;
        for (int i = k + 2; i < n; i++) {
            while (dejaPris.contains(tmp)) {
                tmp++;
            }
            a[i] = decompositionBase10VersBaseP(tmp, p, k + 1);
            tmp++;
        }

        ArrayList<Integer>[] hashTupleSetTable = new ArrayList[k + 1];

        int[][][] aWithoutD = new int[n][k + 1][k];

        int hash;
        HashMap<Integer, Integer>[] ady = new HashMap[k + 1];
        VecInt[] adxd = new VecInt[k + 1];
        int varId;

        for (int d = 0; d < k + 1; d++) {
            hashTupleSetTable[d] = new ArrayList<Integer>();
            ady[d] = new HashMap<Integer, Integer>();
            adxd[d] = new VecInt();
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < k; j++) {
                    if (j < d) {
                        aWithoutD[i][d][j] = a[i][j];
                    } else {
                        aWithoutD[i][d][j] = a[i][j + 1];
                    }
                }
                hash = recompositionBase10DepuisBaseP(aWithoutD[i][d], p);
                if (!hashTupleSetTable[d].contains(hash)) {
                    hashTupleSetTable[d].add(hash);
                    varId = solver.nextFreeVarId(true);
                    ady[d].put(hash, varId);
                    adxd[d].push(varId);
                }
            }
        }

        for (int d = 0; d < k + 1; d++) {
            for (int i = 0; i < n; i++) {
                clause.push(-literals.get(i));
                clause.push(ady[d].get(recompositionBase10DepuisBaseP(
                        aWithoutD[i][d], p)));
                group.add(solver.addClause(clause));
                clause.clear();
            }
            group.add(addAtMost(solver, adxd[d], k));
        }

        return group;
    }

    @Override
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {

        ConstrGroup group = new ConstrGroup(false);

        IVecInt clause = new VecInt();

        final int n = literals.size();

        if (n < 7) {
            Binomial binomial = new Binomial();
            return binomial.addAtMostOne(solver, literals);
        }

        final int p = (int) Math.ceil(Math.sqrt(n));
        final int q = (int) Math.ceil((double) n / (double) p);

        int[] u = new int[p];
        int[] v = new int[q];

        for (int i = 0; i < p; i++) {
            u[i] = solver.nextFreeVarId(true);
        }
        for (int i = 0; i < q; i++) {
            v[i] = solver.nextFreeVarId(true);
        }

        int cpt = 0;
        for (int i = 0; i < p; i++) {
            for (int j = 0; j < q; j++) {
                if (cpt < n) {
                    clause.push(-literals.get(cpt));
                    clause.push(u[i]);
                    group.add(solver.addClause(clause));
                    clause.clear();
                    clause.push(-literals.get(cpt));
                    clause.push(v[j]);
                    group.add(solver.addClause(clause));
                    clause.clear();
                    cpt++;
                }
            }
        }

        group.add(addAtMostOne(solver, new VecInt(u)));
        group.add(addAtMostOne(solver, new VecInt(v)));
        return group;
    }

    private int[] decompositionBase10VersBaseP(int n, int p, int nbBits) {
        int[] result = new int[nbBits];

        int reste;
        int pow;
        int quotient;
        reste = n;
        for (int j = 0; j < nbBits - 1; j++) {
            pow = (int) Math.pow(p, nbBits - j - 1);
            quotient = reste / pow;
            result[j] = quotient + 1;
            reste = reste - quotient * pow;
        }
        result[nbBits - 1] = reste + 1;
        return result;
    }

    private int recompositionBase10DepuisBaseP(int[] tab, int p) {
        int result = 0;
        for (int i = 0; i < tab.length - 1; i++) {
            result = (result + tab[i] - 1) * p;
        }
        result += tab[tab.length - 1] - 1;
        return result;
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
