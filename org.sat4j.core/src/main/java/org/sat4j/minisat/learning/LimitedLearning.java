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
package org.sat4j.minisat.learning;

import org.sat4j.minisat.core.DataStructureFactory;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.LearningStrategy;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.core.SolverStats;
import org.sat4j.minisat.core.VarActivityListener;
import org.sat4j.specs.Constr;

/**
 * Learn only clauses which size is smaller than a percentage of the number of
 * variables.
 * 
 * @author leberre
 */
public abstract class LimitedLearning<D extends DataStructureFactory>
        implements LearningStrategy<D> {

    private static final long serialVersionUID = 1L;

    private final NoLearningButHeuristics<D> none;

    private final MiniSATLearning<D> all;

    protected ILits lits;

    private SolverStats stats;

    public LimitedLearning() {
        this.none = new NoLearningButHeuristics<D>();
        this.all = new MiniSATLearning<D>();
    }

    public void setSolver(Solver<D> s) {
        if (s != null) {
            this.lits = s.getVocabulary();
            setVarActivityListener(s);
            this.all.setDataStructureFactory(s.getDSFactory());
            this.stats = s.getStats();
        }
    }

    public void learns(Constr constr) {
        if (learningCondition(constr)) {
            this.all.learns(constr);
        } else {
            this.none.learns(constr);
            this.stats.incIgnoredclauses();
        }
    }

    protected abstract boolean learningCondition(Constr constr);

    public void init() {
        this.all.init();
        this.none.init();
    }

    public void setVarActivityListener(VarActivityListener s) {
        this.none.setVarActivityListener(s);
        this.all.setVarActivityListener(s);
    }
}
