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
package org.sat4j.minisat.core;

import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;

/**
 * The aim of the factory is to provide a concrete implementation of clauses,
 * cardinality constraints and pseudo boolean consraints.
 * 
 * @author leberre
 */
public interface DataStructureFactory {

    /**
     * @param literals
     *            a set of literals using Dimacs format (signed non null
     *            integers).
     * @return null if the constraint is a tautology.
     * @throws ContradictionException
     *             the constraint is trivially unsatisfiable.
     * @throws UnsupportedOperationException
     *             there is no concrete implementation for that constraint.
     */
    Constr createClause(IVecInt literals) throws ContradictionException;

    Constr createUnregisteredClause(IVecInt literals);

    void learnConstraint(Constr constr);

    /**
     * Create a cardinality constraint of the form sum li &gt;= degree.
     * 
     * @param literals
     *            a set of literals.
     * @param degree
     *            the degree of the cardinality constraint.
     * @return a constraint stating that at least degree literals are satisfied.
     * @throws ContradictionException
     */
    Constr createCardinalityConstraint(IVecInt literals, int degree)
            throws ContradictionException;

    Constr createUnregisteredCardinalityConstraint(IVecInt literals,
            int degree);

    void setUnitPropagationListener(UnitPropagationListener s);

    void setLearner(Learner l);

    void reset();

    ILits getVocabulary();

    /**
     * @param p
     * @return a vector containing all the objects to be notified of the
     *         satisfaction of that literal.
     */
    IVec<Propagatable> getWatchesFor(int p);

    /**
     * @param p
     * @param i
     *            the index of the conflicting constraint
     */
    void conflictDetectedInWatchesFor(int p, int i);
}
