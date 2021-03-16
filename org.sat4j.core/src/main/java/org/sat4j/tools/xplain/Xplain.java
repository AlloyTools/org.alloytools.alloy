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
package org.sat4j.tools.xplain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.FullClauseSelectorSolver;
import org.sat4j.tools.SolverDecorator;

/**
 * Explanation framework for SAT4J.
 * 
 * The explanation uses selector variables and assumptions.
 * 
 * It is based on a two steps method: 1) extraction of a set of assumptions
 * implying the inconsistency 2) minimization of that set.
 * 
 * @author daniel
 * 
 * @param <T>
 *            a subinterface to ISolver.
 * @since 2.1
 */
public class Xplain<T extends ISolver> extends FullClauseSelectorSolver<T>
        implements Explainer {

    private IVecInt assump;

    private MinimizationStrategy xplainStrategy = new DeletionStrategy();

    public Xplain(T solver, boolean skipDuplicatedEntries) {
        super(solver, skipDuplicatedEntries);
    }

    public Xplain(T solver) {
        this(solver, true);
    }

    @Override
    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        throw new UnsupportedOperationException(
                "Explanation requires Pseudo Boolean support. See XplainPB class instead.");
    }

    @Override
    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException(
                "Explanation requires Pseudo Boolean support. See XplainPB class instead.");
    }

    @Override
    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException(
                "Explanation requires Pseudo Boolean support. See XplainPB class instead.");
    }

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * @since 2.2.4
     * @return
     * @throws TimeoutException
     */
    private IVecInt explanationKeys() throws TimeoutException {
        assert !isSatisfiable(this.assump);
        ISolver solver = decorated();
        if (solver instanceof SolverDecorator<?>) {
            solver = ((SolverDecorator<? extends ISolver>) solver).decorated();
        }
        return this.xplainStrategy.explain(solver, getConstrs(), this.assump);
    }

    /**
     * Provide an explanation of the inconsistency in terms of a subset minimal
     * set of constraints, each constraint being referred to as its index
     * (order) in the solver: first constraint is numbered 1, the second 2, etc.
     * 
     * @return an array of indexes such that the set of indexed constraints is
     *         inconsistent.
     * @throws TimeoutException
     * @see #explain()
     */
    public int[] minimalExplanation() throws TimeoutException {
        IVecInt keys = explanationKeys();
        keys.sort();
        List<Integer> allKeys = new ArrayList<Integer>(getConstrs().keySet());
        Collections.sort(allKeys);
        int[] model = new int[keys.size()];
        int i = 0;
        for (IteratorInt it = keys.iterator(); it.hasNext();) {
            model[i++] = allKeys.indexOf(it.next()) + 1;
        }
        return model;
    }

    /**
     * Provide an explanation of the inconsistency in term of a subset minimal
     * set of constraints. Compared to {@link #minimalExplanation()}, the method
     * returns a reference to the constraint object, instead of an index.
     * 
     * @since 2.1
     * @return
     * @throws TimeoutException
     * @see #minimalExplanation()
     */
    public Collection<IConstr> explain() throws TimeoutException {
        IVecInt keys = explanationKeys();
        Collection<IConstr> explanation = new ArrayList<IConstr>(keys.size());
        for (IteratorInt it = keys.iterator(); it.hasNext();) {
            explanation.add(getConstrs().get(it.next()));
        }
        return explanation;
    }

    /**
     * @since 2.1
     */
    public void cancelExplanation() {
        this.xplainStrategy.cancelExplanationComputation();
    }

    @Override
    public int[] findModel() throws TimeoutException {
        this.assump = VecInt.EMPTY;
        return super.findModel();
    }

    @Override
    public int[] findModel(IVecInt assumps) throws TimeoutException {
        this.assump = assumps;
        return super.findModel(assumps);
    }

    @Override
    public boolean isSatisfiable() throws TimeoutException {
        this.assump = VecInt.EMPTY;
        return super.isSatisfiable();
    }

    @Override
    public boolean isSatisfiable(boolean global) throws TimeoutException {
        this.assump = VecInt.EMPTY;
        return super.isSatisfiable(global);
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps) throws TimeoutException {
        this.assump = assumps;
        return super.isSatisfiable(assumps);
    }

    @Override
    public boolean isSatisfiable(IVecInt assumps, boolean global)
            throws TimeoutException {
        this.assump = assumps;
        return super.isSatisfiable(assumps, global);
    }

    @Override
    public String toString(String prefix) {
        System.out.println(prefix + "Explanation (MUS) enabled solver");
        System.out.println(prefix + this.xplainStrategy);
        return super.toString(prefix);
    }

    public void setMinimizationStrategy(MinimizationStrategy strategy) {
        this.xplainStrategy = strategy;
    }

    @Override
    public boolean removeConstr(IConstr c) {
        if (getLastConstr() == c) {
            getLastClause().clear();
            setLastConstr(null);
        }
        return super.removeConstr(c);
    }

    @Override
    public boolean removeSubsumedConstr(IConstr c) {
        if (getLastConstr() == c) {
            getLastClause().clear();
            setLastConstr(null);
        }
        return super.removeSubsumedConstr(c);
    }

}
