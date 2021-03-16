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

import java.util.Map;
import java.util.Set;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;

/**
 * An implementation of the QuickXplain algorithm as explained by Ulrich Junker
 * in the following paper:
 * 
 * <code>
 * &#64;inproceedings{ junker01:quickxplain:inp, author={Ulrich Junker},
 *                 title={QUICKXPLAIN: Conflict Detection for Arbitrary
 *                 Constraint Propagation Algorithms}, booktitle={IJCAI'01
 *                 Workshop on Modelling and Solving problems with constraints
 *                 (CONS-1)}, year={2001}, month={August}, address={Seattle, WA,
 *                 USA}, url={citeseer.ist.psu.edu/junker01quickxplain.html},
 *                 url={http://www.lirmm.fr/~bessiere/ws_ijcai01/junker.ps.gz} }
 * 
 *                 The algorithm has been adapted to work properly in a context
 *                 where we can afford to add a selector variable to each clause
 *                 to enable or disable each constraint.
 * 
 *                 Note that for the moment, QuickXplain does not work properly
 *                 in an optimization setting.
 * </code>
 * 
 * @since 2.1
 */
public class QuickXplain2001Strategy implements MinimizationStrategy {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private boolean computationCanceled;

    public void cancelExplanationComputation() {
        this.computationCanceled = true;
    }

    public IVecInt explain(ISolver solver, Map<Integer, ?> constrs,
            IVecInt assumps) throws TimeoutException {
        this.computationCanceled = false;
        IVecInt encodingAssumptions = new VecInt(
                constrs.size() + assumps.size());
        assumps.copyTo(encodingAssumptions);
        IVecInt firstExplanation = solver.unsatExplanation();
        if (solver.isVerbose()) {
            System.out.print(solver.getLogPrefix() + "initial unsat core ");
            firstExplanation.sort();
            for (IteratorInt it = firstExplanation.iterator(); it.hasNext();) {
                System.out.print(constrs.get(-it.next()));
                System.out.print(" ");
            }
            System.out.println();
        }
        Set<Integer> constraintsVariables = constrs.keySet();
        int p;
        for (int i = 0; i < firstExplanation.size(); i++) {
            if (constraintsVariables.contains(p = -firstExplanation.get(i))) {
                encodingAssumptions.push(p);
            }
        }
        IVecInt results = new VecInt(encodingAssumptions.size());
        computeExplanation(solver, encodingAssumptions, assumps.size(),
                encodingAssumptions.size() - 1, results);
        return results;
    }

    private void computeExplanation(ISolver solver, IVecInt encodingAssumptions,
            int start, int end, IVecInt result) throws TimeoutException {
        if (!solver.isSatisfiable(encodingAssumptions)) {
            return;
        }
        int i = start;
        encodingAssumptions.set(i, -encodingAssumptions.get(i));
        assert encodingAssumptions.get(i) < 0;
        while (!this.computationCanceled
                && solver.isSatisfiable(encodingAssumptions)) {
            if (i == end) {
                for (int j = start; j <= end; j++) {
                    encodingAssumptions.set(j, -encodingAssumptions.get(j));
                }
                return;
            }
            i++;
            assert encodingAssumptions.get(i) > 0;
            encodingAssumptions.set(i, -encodingAssumptions.get(i));
        }
        result.push(-encodingAssumptions.get(i));
        if (start == i) {
            return;
        }
        int newend = i - 1;
        int split = (newend + start) / 2;
        if (split < newend) {
            for (int j = split + 1; j < i; j++) {
                encodingAssumptions.set(j, -encodingAssumptions.get(j));
            }
            computeExplanation(solver, encodingAssumptions, split + 1, newend,
                    result);
        }
        if (start <= split) {
            for (int j = start; j <= split; j++) {
                encodingAssumptions.set(j, -encodingAssumptions.get(j));
            }
            computeExplanation(solver, encodingAssumptions, start, split,
                    result);
        }
        if (this.computationCanceled) {
            throw new TimeoutException();
        }
    }

    @Override
    public String toString() {
        return "QuickXplain (IJCAI WS 2001 version) minimization strategy";
    }
}
