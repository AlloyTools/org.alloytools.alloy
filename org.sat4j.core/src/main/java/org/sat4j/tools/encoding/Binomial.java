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
 * Binomial encoding for the "at most one" and "at most k" cases.
 * 
 * For the "at most one" case, this encoding is equivalent to the one referred
 * to in the literature as the pair-wise or naive encoding. For the "at most k"
 * case, the previous encoding is generalized with binomial selection (see A. M.
 * Frisch and P. A. Giannaros, "SAT Encodings of the At-Most-k Constraint", in
 * International Workshop on Modelling and Reformulating Constraint Satisfaction
 * Problems, 2010 for details).
 * 
 * @author stephanieroussel
 * @since 2.3.1
 */
public class Binomial extends EncodingStrategyAdapter {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    @Override
    public IConstr addAtMost(ISolver solver, IVecInt literals, int degree)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);

        IVecInt clause = new VecInt();

        if (degree == 1) {
            return addAtMostOne(solver, literals);
        }

        for (IVecInt vec : literals.subset(degree + 1)) {
            for (int i = 0; i < vec.size(); i++) {
                clause.push(-vec.get(i));
            }
            group.add(solver.addClause(clause));
            clause.clear();
        }
        return group;

    }

    @Override
    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        ConstrGroup group = new ConstrGroup(false);

        IVecInt clause = new VecInt();

        for (int i = 0; i < literals.size() - 1; i++) {
            for (int j = i + 1; j < literals.size(); j++) {
                clause.push(-literals.get(i));
                clause.push(-literals.get(j));
                group.add(solver.addClause(clause));
                clause.clear();
            }
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
