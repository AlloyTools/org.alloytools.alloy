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
package org.sat4j.specs;

/**
 * This interface is to be implemented by the classes wanted to be notified of
 * the falsification of a literal.
 * 
 * That interface was moved here from org.sat4j.minisat.core package in release
 * 2.3.6 to avoid cyclic dependencies with org.sat4j.specs.
 * 
 * @author leberre
 */
public interface Propagatable {

    /**
     * Propagate the truth value of a literal in constraints in which that
     * literal is falsified.
     * 
     * @param s
     *            something able to perform unit propagation
     * @param p
     *            the literal being propagated. Its negation must appear in the
     *            constraint.
     * @return false iff an inconsistency (a contradiction) is detected.
     */
    boolean propagate(UnitPropagationListener s, int p);

    /**
     * Specific procedure for computing the prime implicants of a formula.
     * 
     * @param l
     *            an object to gather mandatory literals.
     * @param p
     *            the falsified literal
     * @return
     * @since 2.3.6
     */
    boolean propagatePI(MandatoryLiteralListener l, int p);

    /**
     * Allow to access a constraint view of the propagatable to avoid casting.
     * In most cases, the constraint will implement directly propagatable thus
     * will return itself. It will also also the implementation of more
     * sophisticated watching strategy.
     * 
     * @return the constraint associated to that propagatable.
     * @since 2.3.2
     */
    Constr toConstraint();
}
