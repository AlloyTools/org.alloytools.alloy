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

import org.sat4j.annotations.Feature;

/*
 * Created on 16 oct. 2003
 */

/**
 * Basic constraint abstraction used in this solvers.
 * 
 * Any new constraint type should implement that interface.
 * 
 * That interface was moved in this package from org.sat4j.minisat.core package
 * in release 2.3.6 to avoid cyclic dependencies with org.sat4j.specs.
 * 
 * @author leberre
 */
@Feature(value = "constraint", parent = "expert")
public interface Constr extends IConstr {

    Constr TAUTOLOGY = new Constr() {

        public boolean learnt() {
            return false;
        }

        public int size() {
            return 0;
        }

        public int get(int i) {
            throw new UnsupportedOperationException(
                    "No elements in a tautology");
        }

        public double getActivity() {
            return 0.0;
        }

        public boolean canBePropagatedMultipleTimes() {
            return false;
        }

        public String toString(VarMapper mapper) {
            return "TAUT";
        }

        public void remove(UnitPropagationListener upl) {
            // do nothing
        }

        public boolean simplify() {
            return false;
        }

        public void calcReason(int p, IVecInt outReason) {
            throw new UnsupportedOperationException(
                    "A tautology cannot be a reason");
        }

        public void calcReasonOnTheFly(int p, IVecInt trail,
                IVecInt outReason) {
            throw new UnsupportedOperationException(
                    "A tautology cannot be a reason");
        }

        public void incActivity(double claInc) {
            // do nothing
        }

        public void forwardActivity(double claInc) {
            // do nothing
        }

        public boolean locked() {
            return false;
        }

        public void setLearnt() {
            // do nothing
        }

        public void register() {
            // do nothing
        }

        public void rescaleBy(double d) {
            // do nothing
        }

        public void setActivity(double d) {
            // do nothing
        }

        public void assertConstraint(UnitPropagationListener s) {
            // do nothing
        }

        public void assertConstraintIfNeeded(UnitPropagationListener s) {
            // do nothing
        }

        public boolean canBeSatisfiedByCountingLiterals() {
            return false;
        }

        public int requiredNumberOfSatisfiedLiterals() {
            return 0;
        }

        public boolean isSatisfied() {
            return true;
        }

        public int getAssertionLevel(IVecInt trail, int decisionLevel) {
            return 0;
        }

        @Override
        public String dump() {
            return "";
        }
    };

    /**
     * Remove a constraint from the solver.
     * 
     * @param upl
     * @since 2.1
     */
    void remove(UnitPropagationListener upl);

    /**
     * Simplifies a constraint, by removing top level falsified literals for
     * instance.
     * 
     * @return true iff the constraint is satisfied and can be removed from the
     *         database.
     */
    boolean simplify();

    /**
     * Compute the reason for a given assignment.
     * 
     * If the constraint is a clause, it is supposed to be either a unit clause
     * or a falsified one. It is expected that the falsification of the
     * constraint has been detected as soon at is occurs (e.g. using
     * {@link Propagatable#propagate(UnitPropagationListener, int)}.
     * 
     * 
     * @param p
     *            a satisfied literal (or Lit.UNDEFINED)
     * @param outReason
     *            the list of falsified literals whose negation is the reason of
     *            the assignment of p to true.
     */
    void calcReason(int p, IVecInt outReason);

    /**
     * Compute the reason for a given assignment in a the constraint created on
     * the fly in the solver. Compared to the method
     * {@link #calcReason(int, IVecInt)}, the falsification may not have been
     * detected as soon as possible. As such, it is necessary to take into
     * account the order of the literals in the trail.
     * 
     * @param p
     *            a satisfied literal (or Lit.UNDEFINED)
     * @param trail
     *            all the literals satisfied in the solvers, should not be
     *            modified.
     * @param outReason
     *            a list of falsified literals whose negation is the reason of
     *            the assignment of p to true.
     * @since 2.3.3
     */
    void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason);

    /**
     * Increase the constraint activity.
     * 
     * @param claInc
     *            the value to increase the activity with
     */
    void incActivity(double claInc);

    /**
     * 
     * @param claInc
     * @since 2.1
     * 
     */
    @Deprecated
    void forwardActivity(double claInc);

    /**
     * Indicate wether a constraint is responsible from an assignment.
     * 
     * @return true if a constraint is a "reason" for an assignment.
     */
    boolean locked();

    /**
     * Mark a constraint as learnt.
     */

    void setLearnt();

    /**
     * Register the constraint to the solver.
     */
    void register();

    /**
     * Rescale the clause activity by a value.
     * 
     * @param d
     *            the value to rescale the clause activity with.
     */
    void rescaleBy(double d);

    /**
     * Set the activity at a specific value
     * 
     * @param d
     *            the new activity
     * @since 2.3.1
     */
    void setActivity(double d);

    /**
     * Method called when the constraint is to be asserted. It means that the
     * constraint was learned during the search and it should now propagate some
     * truth values. In the clausal case, only one literal should be propagated.
     * In other cases, it might be different.
     * 
     * @param s
     *            a UnitPropagationListener to use for unit propagation.
     */
    void assertConstraint(UnitPropagationListener s);

    /**
     * Method called when the constraint is added to the solver "on the fly". In
     * that case, the constraint may or may not have to propagate some literals,
     * unlike the {@link #assertConstraint(UnitPropagationListener)} method.
     * 
     * @param s
     *            a UnitPropagationListener to use for unit propagation.
     * @since 2.3.4
     */
    void assertConstraintIfNeeded(UnitPropagationListener s);

    /**
     * Check that a specific constraint can be checked for satisfiability by
     * simply counting its number of satisfied literals. This is the case for
     * clauses and cardinality constraints. It is not the case for pseudo
     * boolean constraints.
     * 
     * @return true iff the constraints can be satisfied by satisfying a given
     *         number of literals;
     * @since 2.3.6
     */
    boolean canBeSatisfiedByCountingLiterals();

    /**
     * Returns the number of literals necessary to satisfy that constraint. That
     * method only make sense if the {@link #canBeSatisfiedByCountingLiterals()}
     * returns true. For clauses, the value returned will be 1. For cardinality
     * constraints, the value returned will be its degree.
     * 
     * @return the number of literals
     * @since 2.3.6
     */
    int requiredNumberOfSatisfiedLiterals();

    /**
     * Checks that a constraint is satisfied. That method may be time consuming
     * since it may require to go through all the literals of the constraints.
     * 
     * @return true iff the constraint is satisfied under the current
     *         assignment.
     * @since 2.3.6
     */
    boolean isSatisfied();

    /**
     * Returns the level at which a constraint becomes assertive. Note that if a
     * constraint can propagate multiple times, such method should return the
     * first decision level at which the clause is assertive. Note that the
     * implementation of isAssertive must be in sync with
     * {@link #assertConstraint(UnitPropagationListener)} since the usual step
     * after detecting that a constraint is assertive will be to assert it.
     * 
     * @param trail
     *            the internal solver trail
     * @param decisionLevel
     *            the current decision level
     * @return the decision level under which the constraint becomes assertive,
     *         else -1.
     * @since 2.3.6
     * @see #canBePropagatedMultipleTimes()
     */
    int getAssertionLevel(IVecInt trail, int decisionLevel);
}
