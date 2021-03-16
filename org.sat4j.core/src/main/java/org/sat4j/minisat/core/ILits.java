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
import org.sat4j.specs.IVec;
import org.sat4j.specs.Propagatable;

/**
 * That interface manages the solver's internal vocabulary. Everything related
 * to variables and literals is available from here.
 * 
 * For sake of efficiency, literals and variables are not object in SAT4J. They
 * are represented by numbers. If the vocabulary contains n variables, then
 * variables should be accessed by numbers from 1 to n and literals by numbers
 * from 2 to 2*n+1.
 * 
 * For a Dimacs variable v, the variable index in SAT4J is v, it's positive
 * literal is <code>2*v (v &lt;&lt; 1)</code> and it's negative literal is
 * <code>2*v+1 ((v&lt;&lt;1)^1)</code>. Note that one can easily access to the
 * complementary literal of p by using bitwise operation ^.
 * 
 * In SAT4J, literals are usualy denoted by p or q and variables by v or x.
 * 
 * @author leberre
 */
public interface ILits {

    int UNDEFINED = -1;

    void init(int nvar);

    /**
     * Translates a Dimacs literal into an internal representation literal.
     * 
     * @param x
     *            the Dimacs literal (a non null integer).
     * @return the literal in the internal representation.
     */
    int getFromPool(int x);

    /**
     * Returns true iff the variable is used in the set of constraints.
     * 
     * @param x
     * @return true iff the variable belongs to the formula.
     */
    boolean belongsToPool(int x);

    /**
     * reset the vocabulary.
     */
    void resetPool();

    /**
     * Make sure that all data structures are ready to manage howmany boolean
     * variables.
     * 
     * @param howmany
     *            the new capacity (in boolean variables) of the vocabulary.
     */
    void ensurePool(int howmany);

    /**
     * Unassigns a boolean variable (truth value if UNDEF).
     * 
     * @param lit
     *            a literal in internal format.
     */
    void unassign(int lit);

    /**
     * Satisfies a boolean variable (truth value is TRUE).
     * 
     * @param lit
     *            a literal in internal format.
     */
    void satisfies(int lit);

    /**
     * Removes a variable from the formula. All occurrences of that variables
     * are removed. It is equivalent in our implementation to falsify the two
     * phases of that variable.
     * 
     * @param var
     *            a variable in Dimacs format.
     * @since 2.3.2
     */
    void forgets(int var);

    /**
     * Check if a literal is satisfied.
     * 
     * @param lit
     *            a literal in internal format.
     * @return true if that literal is satisfied.
     */
    boolean isSatisfied(int lit);

    /**
     * Check if a literal is falsified.
     * 
     * @param lit
     *            a literal in internal format.
     * @return true if the literal is falsified. Note that a forgotten variable
     *         will also see its literals as falsified.
     */
    boolean isFalsified(int lit);

    /**
     * Check if a literal is assigned a truth value.
     * 
     * @param lit
     *            a literal in internal format.
     * @return true if the literal is neither satisfied nor falsified.
     */
    boolean isUnassigned(int lit);

    /**
     * @param lit
     * @return true iff the truth value of that literal is due to a unit
     *         propagation or a decision.
     */
    boolean isImplied(int lit);

    /**
     * to obtain the max id of the variable
     * 
     * @return the maximum number of variables in the formula
     */
    int nVars();

    /**
     * to obtain the real number of variables appearing in the formula
     * 
     * @return the number of variables used in the pool
     */
    int realnVars();

    /**
     * Ask the solver for a free variable identifier, in Dimacs format (i.e. a
     * positive number). Note that a previous call to ensurePool(max) will
     * reserve in the solver the variable identifier from 1 to max, so
     * nextFreeVarId() would return max+1, even if some variable identifiers
     * smaller than max are not used.
     * 
     * @return a variable identifier not in use in the constraints already
     *         inside the solver.
     * @since 2.1
     */
    int nextFreeVarId(boolean reserve);

    /**
     * Reset a literal in the vocabulary.
     * 
     * @param lit
     *            a literal in internal representation.
     */
    void reset(int lit);

    /**
     * Returns the level at which that literal has been assigned a value, else
     * -1.
     * 
     * @param lit
     *            a literal in internal representation.
     * @return -1 if the literal is unassigned, or the decision level of the
     *         literal.
     */
    int getLevel(int lit);

    /**
     * Sets the decision level of a literal.
     * 
     * @param lit
     *            a literal in internal representation.
     * @param l
     *            a decision level, or -1
     */
    void setLevel(int lit, int l);

    /**
     * Returns the reason of the assignment of a literal.
     * 
     * @param lit
     *            a literal in internal representation.
     * @return the constraint that propagated that literal, else null.
     */
    Constr getReason(int lit);

    /**
     * Sets the reason of the assignment of a literal.
     * 
     * @param lit
     *            a literal in internal representation.
     * @param r
     *            the constraint that forces the assignment of that literal,
     *            null if there are none.
     */
    void setReason(int lit, Constr r);

    /**
     * Retrieve the methods to call when the solver backtracks. Useful for
     * counter based data structures.
     * 
     * @param lit
     *            a literal in internal representation.
     * @return a list of methods to call on bactracking.
     */
    IVec<Undoable> undos(int lit);

    /**
     * Record a new constraint to watch when a literal is satisfied.
     * 
     * @param lit
     *            a literal in internal representation.
     * @param c
     *            a constraint that contains the negation of that literal.
     */
    void watch(int lit, Propagatable c);

    /**
     * @param lit
     *            a literal in internal representation.
     * @return the list of all the constraints that watch the negation of lit
     */
    IVec<Propagatable> watches(int lit);

    /**
     * Returns a textual representation of the truth value of that literal.
     * 
     * @param lit
     *            a literal in internal representation.
     * @return one of T for true, F for False or ? for unassigned.
     */
    String valueToString(int lit);

    /**
     * set the position in the trail.
     * 
     * @param lit
     *            a literal in internal representation.
     * @param position
     *            the position in the trail
     * @since 2.3.6
     * 
     */
    void setTrailPosition(int lit, int position);

    /**
     * get the position in the trail
     * 
     * @param lit
     *            a literal in internal representation.
     * @return a non negative integer if the literal is assigned, else -1.
     * @since 2.3.6
     */
    int getTrailPosition(int lit);
}
