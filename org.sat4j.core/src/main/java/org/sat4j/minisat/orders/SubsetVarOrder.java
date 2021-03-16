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

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.Heap;

@Feature(value = "varheuristics", parent = "expert")
public class SubsetVarOrder extends VarOrderHeap {

    private final int[] varsToTest;
    private boolean[] inSubset;

    public SubsetVarOrder(int[] varsToTest) {
        this.varsToTest = new int[varsToTest.length];
        System.arraycopy(varsToTest, 0, this.varsToTest, 0, varsToTest.length);
    }

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    @Override
    public void init() {
        int nlength = this.lits.nVars() + 1;
        if (this.activity == null || this.activity.length < nlength) {
            this.activity = new double[nlength];
        }
        this.inSubset = new boolean[nlength];
        this.phaseStrategy.init(nlength);
        this.activity[0] = -1;
        this.heap = new Heap(
                new ActivityBasedVariableComparator(this.activity));
        this.heap.setBounds(nlength);
        for (int var : this.varsToTest) {
            assert var > 0;
            assert var <= this.lits.nVars() : "" + this.lits.nVars() + "/" //$NON-NLS-1$ //$NON-NLS-2$
                    + var;
            this.inSubset[var] = true;
            this.activity[var] = 0.0;
            if (this.lits.belongsToPool(var)) {
                this.heap.insert(var);
            }
        }
    }

    @Override
    public void undo(int x) {
        if (this.inSubset[x] && !this.heap.inHeap(x)) {
            this.heap.insert(x);
        }
    }

}
