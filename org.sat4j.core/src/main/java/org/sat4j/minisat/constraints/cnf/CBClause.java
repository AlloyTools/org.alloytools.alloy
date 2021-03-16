/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
 *******************************************************************************/
package org.sat4j.minisat.constraints.cnf;

import java.io.Serializable;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Undoable;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

/**
 * @author leberre
 */
@Feature("constraint")
public class CBClause implements Constr, Undoable, Propagatable, Serializable {

    private static final long serialVersionUID = 1L;

    protected int falsified;

    private boolean learnt;

    protected final int[] lits;

    protected final ILits voc;

    private double activity;

    public static CBClause brandNewClause(UnitPropagationListener s, ILits voc,
            IVecInt literals) {
        CBClause c = new CBClause(literals, voc);
        c.register();
        return c;
    }

    /**
     * 
     */
    public CBClause(IVecInt ps, ILits voc, boolean learnt) {
        this.learnt = learnt;
        this.lits = new int[ps.size()];
        this.voc = voc;
        ps.moveTo(this.lits);
    }

    public CBClause(IVecInt ps, ILits voc) {
        this(ps, voc, false);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#remove()
     */
    public void remove() {
        for (int i = 0; i < lits.length; i++) {
            voc.watches(lits[i] ^ 1).remove(this);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#propagate(org.sat4j.minisat.core.
     * UnitPropagationListener, int)
     */
    public boolean propagate(UnitPropagationListener s, int p) {
        voc.undos(p).push(this);
        falsified++;
        assert falsified != lits.length;
        if (falsified == lits.length - 1) {
            // find unassigned literal
            for (int i = 0; i < lits.length; i++) {
                if (!voc.isFalsified(lits[i])) {
                    return s.enqueue(lits[i], this);
                }
            }
            // one of the variable in to be propagated to false.
            // (which explains why the falsified counter has not
            // been increased yet)
            return false;
        }
        return true;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#simplify()
     */
    public boolean simplify() {
        for (int p : lits) {
            if (voc.isSatisfied(p)) {
                return true;
            }
        }
        return false;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#undo(int)
     */
    public void undo(int p) {
        falsified--;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#calcReason(int,
     * org.sat4j.specs.VecInt)
     */
    public void calcReason(int p, IVecInt outReason) {
        assert outReason.size() == 0;
        for (int q : lits) {
            assert voc.isFalsified(q) || q == p;
            if (voc.isFalsified(q)) {
                outReason.push(q ^ 1);
            }
        }
        assert (p == ILits.UNDEFINED) || (outReason.size() == lits.length - 1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#learnt()
     */
    public boolean learnt() {
        return learnt;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#incActivity(double)
     */
    public void incActivity(double claInc) {
        activity += claInc;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#getActivity()
     */
    public double getActivity() {
        return activity;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#locked()
     */
    public boolean locked() {
        return voc.getReason(lits[0]) == this;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#setLearnt()
     */
    public void setLearnt() {
        learnt = true;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#register()
     */
    public void register() {
        for (int p : lits) {
            voc.watch(p ^ 1, this);
        }
        if (learnt) {
            for (int p : lits) {
                if (voc.isFalsified(p)) {
                    voc.undos(p ^ 1).push(this);
                    falsified++;
                }
            }
            assert falsified == lits.length - 1;
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#rescaleBy(double)
     */
    public void rescaleBy(double d) {
        activity *= d;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#size()
     */
    public int size() {
        return lits.length;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.Constr#get(int)
     */
    public int get(int i) {
        return lits[i];
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.sat4j.minisat.core.Constr#assertConstraint(org.sat4j.minisat.core
     * .UnitPropagationListener)
     */
    public void assertConstraint(UnitPropagationListener s) {
        assert voc.isUnassigned(lits[0]);
        boolean ret = s.enqueue(lits[0], this);
        assert ret;
    }

    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        for (int i = 0; i < lits.length; i++) {
            stb.append(lits[i]);
            stb.append("["); //$NON-NLS-1$
            stb.append(voc.valueToString(lits[i]));
            stb.append("]"); //$NON-NLS-1$
            stb.append(" "); //$NON-NLS-1$
        }
        return stb.toString();
    }

    public boolean canBePropagatedMultipleTimes() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public String toString(VarMapper mapper) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void remove(UnitPropagationListener upl) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void forwardActivity(double claInc) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void setActivity(double d) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean canBeSatisfiedByCountingLiterals() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int requiredNumberOfSatisfiedLiterals() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean isSatisfied() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public boolean propagatePI(MandatoryLiteralListener l, int p) {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public Constr toConstraint() {
        return this;
    }

    @Override
    public String dump() {
        StringBuilder stb = new StringBuilder();
        for (int p : lits) {
            stb.append(LiteralsUtils.toDimacs(p));
            stb.append(' ');
        }
        stb.append('0');
        return stb.toString();
    }
}
