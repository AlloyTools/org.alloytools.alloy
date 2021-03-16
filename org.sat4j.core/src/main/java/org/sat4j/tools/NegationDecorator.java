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
import java.util.Collection;

import org.sat4j.annotations.Feature;
import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;

/**
 * Negates the formula inside a solver.
 * 
 * @author leberre
 * 
 * @param <T>
 */
@Feature("solver")
public class NegationDecorator<T extends ISolver>
        extends AbstractClauseSelectorSolver<T> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final Collection<Integer> addedVars = new ArrayList<Integer>();

    public NegationDecorator(T decorated) {
        super(decorated);
        internalState();
    }

    @Override
    public IConstr addClause(IVecInt literals) throws ContradictionException {
        int newVar = createNewVar(literals);
        IVecInt clause = new VecInt(2);
        clause.push(newVar);
        ConstrGroup group = new ConstrGroup();
        for (IteratorInt it = literals.iterator(); it.hasNext();) {
            clause.push(-it.next());
            group.add(super.addClause(clause));
            clause.pop();
        }
        addedVars.add(newVar);
        return group;
    }

    @Override
    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps, boolean global)
            throws TimeoutException {
        IVecInt vars = new VecInt();
        for (int var : getAddedVars()) {
            vars.push(var);
        }
        try {
            IConstr constr = super.addClause(vars);
            boolean returnValue;
            try {
                returnValue = super.isSatisfiable(assumps, global);
            } finally {
                removeConstr(constr);
            }
            return returnValue;
        } catch (ContradictionException e) {
            return false;
        }

    }

    @Override
    public Collection<Integer> getAddedVars() {
        return addedVars;
    }

}
