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
package org.sat4j.tools;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IGroupSolver;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

@Feature("solver")
public class GroupClauseSelectorSolver<T extends ISolver>
        extends AbstractClauseSelectorSolver<T> implements IGroupSolver {

    private static final long serialVersionUID = 1L;

    private final Map<Integer, Integer> varToHighLevel = new HashMap<Integer, Integer>();
    private final Map<Integer, Integer> highLevelToVar = new HashMap<Integer, Integer>();

    public GroupClauseSelectorSolver(T solver) {
        super(solver);
    }

    public IConstr addControlableClause(IVecInt literals, int desc)
            throws ContradictionException {
        if (desc == 0) {
            return super.addClause(literals);
        }
        Integer hlvar = getGroupVar(literals, desc);
        literals.push(hlvar);
        return super.addClause(literals);
    }

    protected Integer getGroupVar(IVecInt literals, int groupid) {
        Integer hlvar = this.highLevelToVar.get(groupid);
        if (hlvar == null) {
            hlvar = createNewVar(literals);
            this.highLevelToVar.put(groupid, hlvar);
            this.varToHighLevel.put(hlvar, groupid);
        }
        return hlvar;
    }

    public IConstr addNonControlableClause(IVecInt literals)
            throws ContradictionException {
        return super.addClause(literals);
    }

    public IConstr addClause(IVecInt literals, int desc)
            throws ContradictionException {
        return addControlableClause(literals, desc);
    }

    @Override
    public Collection<Integer> getAddedVars() {
        return varToHighLevel.keySet();
    }

    @Override
    public int[] model() {
        int[] fullmodel = super.modelWithInternalVariables();
        if (fullmodel == null) {
            return null;
        }
        int[] model = new int[fullmodel.length - this.varToHighLevel.size()];
        int j = 0;
        for (int element : fullmodel) {
            if (this.varToHighLevel.get(Math.abs(element)) == null) {
                model[j++] = element;
            }
        }
        return model;
    }

    public Map<Integer, Integer> getVarToHighLevel() {
        return varToHighLevel;
    }

    @Override
    public IVecInt unsatExplanation() {
        IVecInt internal = super.unsatExplanation();
        IVecInt external = new VecInt(internal.size());
        int p;
        Integer group;
        for (IteratorInt it = internal.iterator(); it.hasNext();) {
            p = it.next();
            if (p > 0) {
                group = varToHighLevel.get(p);
            } else {
                Integer negGroup = varToHighLevel.get(-p);
                group = (negGroup == null) ? (null) : (-negGroup);
            }
            if (group != null) {
                external.push(group);
            }
        }
        return external;
    }

}
