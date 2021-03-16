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
package org.sat4j.core;

import org.sat4j.annotations.Feature;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.VarMapper;

/**
 * A utility class used to manage easily group of clauses to be deleted at some
 * point in the solver.
 * 
 * @author dlb
 * @since 2.0
 * 
 */
@Feature("constraint")
public class ConstrGroup implements IConstr {

    private final IVec<IConstr> constrs = new Vec<IConstr>();
    private final boolean disallowNullConstraints;

    /**
     * Create a ConstrGroup that cannot contain null constrs.
     */
    public ConstrGroup() {
        this(true);
    }

    /**
     * Create a new constrGroup.
     * 
     * @param disallowNullConstraints
     *            should be set to false to allow adding null constraints to the
     *            group.
     */
    public ConstrGroup(boolean disallowNullConstraints) {
        this.disallowNullConstraints = disallowNullConstraints;
    }

    public void add(IConstr constr) {
        if (constr == null && this.disallowNullConstraints) {
            throw new IllegalArgumentException(
                    "The constraint you entered cannot be removed from the solver.");
        }
        this.constrs.push(constr);
    }

    public void clear() {
        this.constrs.clear();
    }

    public void removeFrom(ISolver solver) {
        for (int i = constrs.size() - 1; i >= 0; i--) {
            solver.removeConstr(constrs.get(i));
        }
    }

    public IConstr getConstr(int i) {
        return this.constrs.get(i);
    }

    public int size() {
        return this.constrs.size();
    }

    public boolean learnt() {
        if (this.constrs.size() == 0) {
            return false;
        }
        return this.constrs.get(0).learnt();
    }

    public double getActivity() {
        return 0;
    }

    public int get(int i) {
        throw new UnsupportedOperationException();
    }

    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    @Override
    public String toString() {
        return this.constrs.toString();
    }

    public String toString(VarMapper mapper) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String dump() {
        StringBuilder stb = new StringBuilder();
        for (int i = 0; i < constrs.size(); i++) {
            stb.append(constrs.get(i).dump());
            if (i < constrs.size() - 1) {
                stb.append(System.lineSeparator());
            }
        }
        return stb.toString();
    }
}
