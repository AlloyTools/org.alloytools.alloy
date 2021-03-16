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

@Feature("searchlistener")
public abstract class SearchListenerAdapter<S extends ISolverService>
        implements SearchListener<S> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public void init(S solverService) {
    }

    public void assuming(int p) {
    }

    public void propagating(int p) {
    }

    public void enqueueing(int p, IConstr reason) {
    }

    public void backtracking(int p) {
    }

    public void adding(int p) {
    }

    public void learn(IConstr c) {
    }

    public void learnUnit(int p) {
    }

    public void delete(IConstr c) {
    }

    public void conflictFound(IConstr confl, int dlevel, int trailLevel) {
    }

    public void conflictFound(int p) {
    }

    public void solutionFound(int[] model, RandomAccessModel lazyModel) {
    }

    public void beginLoop() {
    }

    public void start() {
    }

    public void end(Lbool result) {
    }

    public void restarting() {
    }

    public void backjump(int backjumpLevel) {
    }

    public void cleaning() {
    }

}
