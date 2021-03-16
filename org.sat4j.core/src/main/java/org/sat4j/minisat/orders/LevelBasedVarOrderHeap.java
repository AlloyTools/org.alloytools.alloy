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
package org.sat4j.minisat.orders;

import java.util.ArrayList;
import java.util.List;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.specs.IVecInt;

/**
 * This heuristic allows to order the selection of the variables using different
 * levels.
 * 
 * @author leberre
 *
 */
@Feature(value = "varheuristics", parent = "expert")
public class LevelBasedVarOrderHeap extends VarOrderHeap {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private int[] level;

    private final List<IVecInt> varsByLevel = new ArrayList<IVecInt>();

    public LevelBasedVarOrderHeap() {
    }

    public LevelBasedVarOrderHeap(IPhaseSelectionStrategy strategy) {
        super(strategy);
    }

    @Override
    protected Heap createHeap(double[] activity) {
        return new Heap(
                new LevelAndActivityVariableComparator(activity, level));
    }

    /**
     * Add a new level with vars
     * 
     * @param vars
     */
    public void addLevel(IVecInt vars) {
        this.varsByLevel.add(vars.clone());
    }

    public void addLevel(int[] vars) {
        this.varsByLevel.add(new VecInt(vars));
    }

    @Override
    public void init() {
        // fill in level array
        int nlength = this.lits.nVars() + 1;
        if (level == null || level.length < nlength) {
            this.level = new int[nlength];
            for (int i = 0; i < nlength; i++) {
                level[i] = Integer.MAX_VALUE;
            }
        }
        IVecInt currentLevel;
        for (int i = 1; i <= varsByLevel.size(); i++) {
            currentLevel = varsByLevel.get(i - 1);
            for (int j = 0; j < currentLevel.size(); j++) {
                level[currentLevel.get(j)] = i;
            }
        }
        super.init();
    }

    @Override
    public String toString() {
        return "Level and activity based heuristics using a heap " //$NON-NLS-1$
                + this.phaseStrategy;
    }

}
