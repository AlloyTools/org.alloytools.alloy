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
package org.sat4j.minisat.constraints.cnf;

import org.sat4j.annotations.Feature;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

/**
 * @since 2.1
 */
@Feature("constraint")
public class UnitClauses implements Constr {

    protected final int[] literals;

    public UnitClauses(IVecInt values) {
        this.literals = new int[values.size()];
        values.copyTo(this.literals);
    }

    public void assertConstraint(UnitPropagationListener s) {
        for (int p : this.literals) {
            s.enqueue(p, this);
        }
    }

    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        assertConstraint(s);
    }

    public void calcReason(int p, IVecInt outReason) {
        throw new UnsupportedOperationException();

    }

    public double getActivity() {
        throw new UnsupportedOperationException();
    }

    public void incActivity(double claInc) {
        // silent to prevent problems with xplain trick.
    }

    public void setActivity(double claInc) {
        // do nothing
    }

    public boolean locked() {
        throw new UnsupportedOperationException();
    }

    public void register() {
        throw new UnsupportedOperationException();
    }

    public void remove(UnitPropagationListener upl) {
        int oldLevel = upl.getPropagationLevel();
        for (int i = this.literals.length - 1; i >= 0; i--) {
            upl.unset(this.literals[i]);
        }
        if (upl.getPropagationLevel() < oldLevel - literals.length) {
            throw new IllegalStateException(
                    "removed unit clause which caused propagations");
        }
    }

    public void rescaleBy(double d) {
        throw new UnsupportedOperationException();
    }

    public void setLearnt() {
        throw new UnsupportedOperationException();
    }

    public boolean simplify() {
        return false;
    }

    public boolean propagate(UnitPropagationListener s, int p) {
        throw new UnsupportedOperationException();
    }

    public int get(int i) {
        throw new UnsupportedOperationException();
    }

    public boolean learnt() {
        throw new UnsupportedOperationException();
    }

    public int size() {
        throw new UnsupportedOperationException();
    }

    public void forwardActivity(double claInc) {
        // silent to prevent problems with xplain trick.
    }

    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        calcReason(p, outReason);
    }

    public void propagatePi(MandatoryLiteralListener m) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean canBeSatisfiedByCountingLiterals() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int requiredNumberOfSatisfiedLiterals() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfied() {
        return true;
    }

    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public String toString(VarMapper mapper) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public String dump() {
        StringBuilder stb = new StringBuilder();
        for (int i = 0; i < literals.length; i++) {
            stb.append(literals[i]);
            stb.append(" 0");
            if (i < literals.length - 1) {
                stb.append(System.lineSeparator());
            }
        }
        return stb.toString();
    }
}
