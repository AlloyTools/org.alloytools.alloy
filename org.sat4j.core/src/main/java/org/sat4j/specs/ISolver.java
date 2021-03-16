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

import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.Map;

import org.sat4j.annotations.Feature;

/**
 * This interface contains all services provided by a SAT solver.
 * 
 * @author leberre
 */
@Feature("solver")
public interface ISolver extends IProblem, Serializable {

    /**
     * Create a new variable in the solver (and thus in the vocabulary).
     * 
     * WE STRONGLY ENCOURAGE TO PRECOMPUTE THE NUMBER OF VARIABLES NEEDED AND TO
     * USE newVar(howmany) INSTEAD. IF YOU EXPERIENCE A PROBLEM OF EFFICIENCY
     * WHEN READING/BUILDING YOUR SAT INSTANCE, PLEASE CHECK THAT YOU ARE NOT
     * USING THAT METHOD.
     * 
     * @return the number of variables available in the vocabulary, which is the
     *         identifier of the new variable.
     */
    @Deprecated
    int newVar();

    /**
     * Ask the solver for a free variable identifier, in Dimacs format (i.e. a
     * positive number). Note that a previous call to newVar(max) will reserve
     * in the solver the variable identifier from 1 to max, so nextFreeVarId()
     * would return max+1, even if some variable identifiers smaller than max
     * are not used. By default, the method will always answer by the maximum
     * variable identifier used so far + 1.
     * 
     * The number of variables reserved in the solver is accessible through the
     * {@link #realNumberOfVariables()} method.
     * 
     * @param reserve
     *            if true, the maxVarId is updated in the solver, i.e.
     *            successive calls to nextFreeVarId(true) will return increasing
     *            variable id while successive calls to nextFreeVarId(false)
     *            will always answer the same.
     * @return a variable identifier not in use in the constraints already
     *         inside the solver.
     * @see #realNumberOfVariables()
     * @since 2.1
     */
    int nextFreeVarId(boolean reserve);

    /**
     * Tell the solver to consider that the literal is in the CNF.
     * 
     * Since model() only return the truth value of the literals that appear in
     * the solver, it is sometimes required that the solver provides a default
     * truth value for a given literal. This happens for instance for MaxSat.
     * 
     * @param p
     *            the literal in Dimacs format that should appear in the model.
     */
    void registerLiteral(int p);

    /**
     * To inform the solver of the expected number of clauses to read. This is
     * an optional method, that is called when the <code>p cnf</code> line is
     * read in dimacs formatted input file.
     * 
     * Note that this method is supposed to be called AFTER a call to
     * newVar(int)
     * 
     * @param nb
     *            the expected number of clauses.
     * @see #newVar(int)
     * @since 1.6
     */
    void setExpectedNumberOfClauses(int nb);

    /**
     * Create a clause from a set of literals The literals are represented by
     * non null integers such that opposite literals a represented by opposite
     * values. (classical Dimacs way of representing literals).
     * 
     * @param literals
     *            a set of literals
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains only
     *             falsified literals after unit propagation
     * @see #removeConstr(IConstr)
     */
    IConstr addClause(IVecInt literals) throws ContradictionException;

    /**
     * Add a clause in order to prevent an assignment to occur. This happens
     * usually when iterating over models for instance.
     * 
     * @param literals
     * @return
     * @throws ContradictionException
     * @since 2.1
     */
    IConstr addBlockingClause(IVecInt literals) throws ContradictionException;

    /**
     * Discards current model. This can be used when iterating on models instead
     * of adding a blocking clause.
     * 
     * @return
     * @throws ContradictionException
     */
    IConstr discardCurrentModel() throws ContradictionException;

    /**
     * Creates a VecInt representing a clause for discarding current model
     * 
     * @return
     */
    IVecInt createBlockingClauseForCurrentModel();

    /**
     * Remove a constraint returned by one of the add method from the solver.
     * All learned clauses will be cleared.
     * 
     * Current implementation does not handle properly the case of unit clauses.
     * 
     * @param c
     *            a constraint returned by one of the add method.
     * @return true if the constraint was successfully removed.
     */
    boolean removeConstr(IConstr c);

    /**
     * Remove a constraint returned by one of the add method from the solver
     * that is subsumed by a constraint already in the solver or to be added to
     * the solver.
     * 
     * Unlike the removeConstr() method, learned clauses will NOT be cleared.
     * 
     * That method is expected to be used to remove constraints used in the
     * optimization process.
     * 
     * In order to prevent a wrong from the user, the method will only work if
     * the argument is the last constraint added to the solver. An illegal
     * argument exception will be thrown in other cases.
     * 
     * @param c
     *            a constraint returned by one of the add method. It must be the
     *            latest constr added to the solver.
     * @return true if the constraint was successfully removed.
     * @since 2.1
     */
    boolean removeSubsumedConstr(IConstr c);

    /**
     * Create clauses from a set of set of literals. This is convenient to
     * create in a single call all the clauses (mandatory for the distributed
     * version of the solver). It is mainly a loop to addClause().
     * 
     * @param clauses
     *            a vector of set (VecInt) of literals in the dimacs format. The
     *            vector can be reused since the solver is not supposed to keep
     *            a reference to that vector.
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains only
     *             falsified literals after unit propagation
     * @see #addClause(IVecInt)
     */
    void addAllClauses(IVec<IVecInt> clauses) throws ContradictionException;

    /**
     * Create a cardinality constraint of the type "at most n of those literals
     * must be satisfied"
     * 
     * @param literals
     *            a set of literals The vector can be reused since the solver is
     *            not supposed to keep a reference to that vector.
     * @param degree
     *            the degree (n) of the cardinality constraint
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains more
     *             than degree satisfied literals after unit propagation
     * @see #removeConstr(IConstr)
     */

    IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException;

    /**
     * Create a cardinality constraint of the type "at least n of those literals
     * must be satisfied"
     * 
     * @param literals
     *            a set of literals. The vector can be reused since the solver
     *            is not supposed to keep a reference to that vector.
     * @param degree
     *            the degree (n) of the cardinality constraint
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if degree literals are
     *             not remaining unfalsified after unit propagation
     * @see #removeConstr(IConstr)
     */
    IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException;

    /**
     * Create a cardinality constraint of the type "exactly n of those literals
     * must be satisfied".
     * 
     * @param literals
     *            a set of literals. The vector can be reused since the solver
     *            is not supposed to keep a reference to that vector.
     * @param n
     *            the number of literals that must be satisfied
     * @return a reference to the constraint added to the solver. It might
     *         return an object representing a group of constraints.
     * @throws ContradictionException
     *             iff the constraint is trivially unsatisfiable.
     * @since 2.3.1
     */
    IConstr addExactly(IVecInt literals, int n) throws ContradictionException;

    /**
     * Add a parity constraint (aka XOR constraint) to the solver.
     * 
     * The aim of that constraint is to enforce that an odd (or even) number of
     * literals are satisfied.
     *
     * If the xor of all the literals results in false, that the number of
     * satisfied literals must be even, else it must be odd.
     * 
     * @since 2.3.6
     */
    IConstr addParity(IVecInt literals, boolean even);

    /**
     * Add a user defined constraint to the solver.
     * 
     * @param constr
     *            a constraint implementing the Constr interface.
     * @return a reference to the constraint for external use.
     * @since 2.3.6
     */
    IConstr addConstr(Constr constr);

    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * @param t
     *            the timeout (in s)
     */
    void setTimeout(int t);

    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * Here the timeout is given in number of conflicts. That way, the behavior
     * of the solver should be the same across different architecture.
     * 
     * @param count
     *            the timeout (in number of conflicts)
     */
    void setTimeoutOnConflicts(int count);

    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * @param t
     *            the timeout (in milliseconds)
     */
    void setTimeoutMs(long t);

    /**
     * Useful to check the internal timeout of the solver.
     * 
     * @return the internal timeout of the solver (in seconds)
     */
    int getTimeout();

    /**
     * Useful to check the internal timeout of the solver.
     * 
     * @return the internal timeout of the solver (in milliseconds)
     * @since 2.1
     */
    long getTimeoutMs();

    /**
     * Expire the timeout of the solver.
     */
    void expireTimeout();

    /**
     * Clean up the internal state of the solver.
     * 
     * Note that such method should also be called when you no longer need the
     * solver because the state of the solver may prevent the GC to proceed.
     * There is a known issue for instance where failing to call reset() on a
     * solver will keep timer threads alive and exhausts memory.
     */
    void reset();

    /**
     * Display statistics to the given output stream Please use writers instead
     * of stream.
     * 
     * @param out
     * @param prefix
     *            the prefix to put in front of each line
     * @see #printStat(PrintWriter, String)
     */
    @Deprecated
    void printStat(PrintStream out, String prefix);

    /**
     * Display statistics to the given output writer
     * 
     * @param out
     * @param prefix
     *            the prefix to put in front of each line
     * @since 1.6
     * @deprecated using the prefix does no longer makes sense because the
     *             solver owns it.
     */
    @Deprecated
    void printStat(PrintWriter out, String prefix);

    /**
     * Display statistics to the given output writer
     * 
     * @param out
     * @since 2.3.3
     * 
     * @see #setLogPrefix(String)
     */
    void printStat(PrintWriter out);

    /**
     * To obtain a map of the available statistics from the solver. Note that
     * some keys might be specific to some solvers.
     * 
     * @return a Map with the name of the statistics as key.
     */
    Map<String, Number> getStat();

    /**
     * Display a textual representation of the solver configuration.
     * 
     * @param prefix
     *            the prefix to use on each line.
     * @return a textual description of the solver internals.
     */
    String toString(String prefix);

    /**
     * Remove clauses learned during the solving process.
     */
    void clearLearntClauses();

    /**
     * Set whether the solver is allowed to simplify the formula by propagating
     * the truth value of top level satisfied variables.
     * 
     * Note that the solver should not be allowed to perform such simplification
     * when constraint removal is planned.
     */
    void setDBSimplificationAllowed(boolean status);

    /**
     * Indicate whether the solver is allowed to simplify the formula by
     * propagating the truth value of top level satisfied variables.
     * 
     * Note that the solver should not be allowed to perform such simplification
     * when constraint removal is planned.
     */
    boolean isDBSimplificationAllowed();

    /**
     * Allow the user to hook a listener to the solver to be notified of the
     * main steps of the search process.
     * 
     * @param sl
     *            a Search Listener.
     * @since 2.1
     */
    <S extends ISolverService> void setSearchListener(SearchListener<S> sl);

    /**
     * Allow the solver to ask for unit clauses before each restarts.
     * 
     * @param ucp
     *            an object able to provide unit clauses.
     * @since 2.3.4
     */
    void setUnitClauseProvider(UnitClauseProvider ucp);

    /**
     * Allow the solver to communicate the unit clauses it learns.
     * 
     * @param ucc
     *            an object interested in unit clauses.
     * @since 2.3.6
     */
    void setUnitClauseConsumer(UnitClauseConsumer ucc);

    /**
     * Get the current SearchListener.
     * 
     * @return a Search Listener.
     * @since 2.2
     */
    <S extends ISolverService> SearchListener<S> getSearchListener();

    /**
     * To know if the solver is in verbose mode (output allowed) or not.
     * 
     * @return true if the solver is verbose.
     * @since 2.2
     */
    boolean isVerbose();

    /**
     * Set the verbosity of the solver
     * 
     * @param value
     *            true to allow the solver to output messages on the console,
     *            false either.
     * @since 2.2
     */
    void setVerbose(boolean value);

    /**
     * Set the prefix used to display information.
     * 
     * @param prefix
     *            the prefix to be in front of each line of text
     * @since 2.2
     */
    void setLogPrefix(String prefix);

    /**
     * 
     * @return the string used to prefix the output.
     * @since 2.2
     */
    String getLogPrefix();

    /**
     * 
     * Retrieve an explanation of the inconsistency in terms of assumption
     * literals. This is only application when isSatisfiable(assumps) is used.
     * Note that
     * <code>!isSatisfiable(assumps)&amp;&amp;assumps.contains(unsatExplanation())</code>
     * should hold.
     * 
     * @return a subset of the assumptions used when calling
     *         isSatisfiable(assumps). Will return null if not applicable (i.e.
     *         no assumptions used).
     * @see #isSatisfiable(IVecInt)
     * @see #isSatisfiable(IVecInt, boolean)
     * @since 2.2
     */
    IVecInt unsatExplanation();

    /**
     * That method is designed to be used to retrieve the real model of the
     * current set of constraints, i.e. to provide the truth value of boolean
     * variables used internally in the solver (for encoding purposes for
     * instance).
     * 
     * If no variables are added in the solver, then
     * Arrays.equals(model(),modelWithInternalVariables()).
     * 
     * In case new variables are added to the solver, then the number of models
     * returned by that method is greater of equal to the number of models
     * returned by model() when using a ModelIterator.
     * 
     * @return an array of literals, in Dimacs format, corresponding to a model
     *         of the formula over all the variables declared in the solver.
     * @see #model()
     * @see org.sat4j.tools.ModelIterator
     * @since 2.3.1
     */
    int[] modelWithInternalVariables();

    /**
     * Retrieve the real number of variables used in the solver.
     * 
     * In many cases, <code>realNumberOfVariables()==nVars()</code>. However,
     * when working with SAT encodings or translation from MAXSAT to PMS, one
     * can have <code>realNumberOfVariables()&gt;nVars()</code>.
     * 
     * Those additional variables are supposed to be created using the
     * {@link #nextFreeVarId(boolean)} method.
     * 
     * @return the number of variables reserved in the solver.
     * @see #nextFreeVarId(boolean)
     * @since 2.3.1
     */
    int realNumberOfVariables();

    /**
     * Ask to the solver if it is in "hot" mode, meaning that the heuristics is
     * not reset after call is isSatisfiable(). This is only useful in case of
     * repeated calls to the solver with same set of variables.
     * 
     * @return true iff the solver keep the heuristics value unchanged across
     *         calls.
     * @since 2.3.2
     */
    boolean isSolverKeptHot();

    /**
     * Changed the behavior of the SAT solver heuristics between successive
     * calls. If the value is true, then the solver will be "hot" on reuse, i.e.
     * the heuristics will not be reset. Else the heuristics will be reset.
     * 
     * @param keepHot
     *            true to keep the heuristics values across calls, false either.
     * @since 2.3.2
     */
    void setKeepSolverHot(boolean keepHot);

    /**
     * Retrieve the real engine in case the engine is decorated by one or
     * several decorator. This can be used for instance to setup the engine,
     * which requires to bypass all the decorators.
     * 
     * It is thus safe to downcast the ISolver to an ICDCL interface. We cannot
     * directly return an ICDCL object because we are not on the same
     * abstraction level here.
     * 
     * @return the solver
     * @since 2.3.3
     */
    ISolver getSolvingEngine();

    /**
     * Check with the solver if the value of that literal was heuristically set
     * or due to constraint propagation.
     * 
     * @param p
     *            a literal
     * @return true iff that literal was propagated by a constraint
     * @see #model()
     * @since 2.3.6
     */
    AssignmentOrigin getOriginInModel(int p);
}
