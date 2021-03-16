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

import java.io.Serializable;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * The aim of this class is to use different encodings for specific constraints.
 * The class is abstract because it does not makes sense to use it "as is".
 * 
 * @author sroussel
 * @since 2.3.1
 */
public abstract class EncodingStrategyAdapter implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public IConstr addAtLeast(ISolver solver, IVecInt literals, int degree)
            throws ContradictionException {
        final int n = literals.size();
        IVecInt newLiterals = new VecInt(n);
        for (int i = 0; i < n; i++) {
            newLiterals.push(-literals.get(i));
        }
        return this.addAtMost(solver, newLiterals, n - degree);
    }

    public IConstr addAtLeastOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        return solver.addClause(literals);
    }

    public IConstr addAtMost(ISolver solver, IVecInt literals, int degree)
            throws ContradictionException {
        return solver.addAtMost(literals, degree);
    }

    public IConstr addAtMostOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        return this.addAtMost(solver, literals, 1);
    }

    public IConstr addExactly(ISolver solver, IVecInt literals, int degree)
            throws ContradictionException {
        return solver.addExactly(literals, degree);
    }

    public IConstr addExactlyOne(ISolver solver, IVecInt literals)
            throws ContradictionException {
        return this.addExactly(solver, literals, 1);
    }

    @Override
    public String toString() {
        return this.getClass().getName();
    }

}
