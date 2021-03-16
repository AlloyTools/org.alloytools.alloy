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

import static org.sat4j.core.LiteralsUtils.var;

import java.io.Serializable;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.ILits;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

/**
 * Lazy data structure for clause using Watched Literals.
 * 
 * @author leberre
 */
@Feature("constraint")
public abstract class WLClause implements Propagatable, Constr, Serializable {

    private static final long serialVersionUID = 1L;

    /**
     * @since 2.1
     */
    protected double activity;

    protected final int[] lits;

    protected final ILits voc;

    /**
     * Creates a new basic clause
     * 
     * @param voc
     *            the vocabulary of the formula
     * @param ps
     *            A VecInt that WILL BE EMPTY after calling that method.
     */
    public WLClause(IVecInt ps, ILits voc) {
        this.lits = new int[ps.size()];
        ps.moveTo(this.lits);
        assert ps.size() == 0;
        this.voc = voc;
        this.activity = 0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see Constr#calcReason(Solver, Lit, Vec)
     */
    public void calcReason(int p, IVecInt outReason) {
        // assert outReason.size() == 0
        // && ((p == ILits.UNDEFINED) || (p == lits[0]));
        final int[] mylits = this.lits;
        for (int i = p == ILits.UNDEFINED ? 0 : 1; i < mylits.length; i++) {
            assert this.voc.isFalsified(mylits[i]);
            outReason.push(mylits[i] ^ 1);
        }
    }

    /**
     * @since 2.1
     */
    public void remove(UnitPropagationListener upl) {
        this.voc.watches(this.lits[0] ^ 1).remove(this);
        this.voc.watches(this.lits[1] ^ 1).remove(this);
        // la clause peut etre effacee
    }

    /*
     * (non-Javadoc)
     * 
     * @see Constr#simplify(Solver)
     */
    public boolean simplify() {
        for (int lit : this.lits) {
            if (this.voc.isSatisfied(lit)) {
                return true;
            }
        }
        return false;
    }

    public boolean propagate(UnitPropagationListener s, int p) {
        final int[] mylits = this.lits;
        // Lits[1] must contain a falsified literal
        if (mylits[0] == (p ^ 1)) {
            mylits[0] = mylits[1];
            mylits[1] = p ^ 1;
        }
        // assert mylits[1] == (p ^ 1);
        if (this.voc.isSatisfied(mylits[0])) {
            this.voc.watch(p, this);
            return true;
        }
        int previous = p ^ 1, tmp;
        // look for new literal to watch: applying move to front strategy
        for (int i = 2; i < mylits.length; i++) {
            if (this.voc.isFalsified(mylits[i])) {
                tmp = previous;
                previous = mylits[i];
                mylits[i] = tmp;
            } else {
                mylits[1] = mylits[i];
                mylits[i] = previous;
                this.voc.watch(mylits[1] ^ 1, this);
                return true;
            }
        }
        // assert voc.isFalsified(mylits[1]);
        // the clause is now either unit or null
        // move back the literals to their initial position
        System.arraycopy(mylits, 2, mylits, 1, mylits.length - 2);
        mylits[mylits.length - 1] = previous;
        this.voc.watch(p, this);
        // propagates first watched literal
        return s.enqueue(mylits[0], this);
    }

    /*
     * For learnt clauses only @author leberre
     */
    public boolean locked() {
        return this.voc.getReason(this.lits[0]) == this;
    }

    /**
     * @return the activity of the clause
     */
    public double getActivity() {
        return this.activity;
    }

    public void setActivity(double d) {
        this.activity = d;
    }

    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        for (int lit : this.lits) {
            stb.append(Lits.toString(lit));
            stb.append("["); //$NON-NLS-1$
            stb.append(this.voc.valueToString(lit));
            stb.append("@");
            stb.append(this.voc.getLevel(lit));
            stb.append("]"); //$NON-NLS-1$
            stb.append(" "); //$NON-NLS-1$
        }
        return stb.toString();
    }

    public String toString(VarMapper mapper) {
        if (mapper == null) {
            return toString();
        }
        StringBuilder stb = new StringBuilder();
        for (int lit : this.lits) {
            stb.append(mapper.map(LiteralsUtils.toDimacs(lit)));
            stb.append("["); //$NON-NLS-1$
            stb.append(this.voc.valueToString(lit));
            stb.append("@");
            stb.append(this.voc.getLevel(lit));
            stb.append("]"); //$NON-NLS-1$
            stb.append(" "); //$NON-NLS-1$
        }
        return stb.toString();
    }

    /**
     * Retourne le ieme literal de la clause. Attention, cet ordre change durant
     * la recherche.
     * 
     * @param i
     *            the index of the literal
     * @return the literal
     */
    public int get(int i) {
        return this.lits[i];
    }

    /**
     * @param d
     */
    public void rescaleBy(double d) {
        this.activity *= d;
    }

    public int size() {
        return this.lits.length;
    }

    public void assertConstraint(UnitPropagationListener s) {
        boolean ret = s.enqueue(this.lits[0], this);
        assert ret;
    }

    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        if (voc.isFalsified(this.lits[1])) {
            boolean ret = s.enqueue(this.lits[0], this);
            assert ret;
        }
    }

    public ILits getVocabulary() {
        return this.voc;
    }

    public int[] getLits() {
        int[] tmp = new int[size()];
        System.arraycopy(this.lits, 0, tmp, 0, size());
        return tmp;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        try {
            WLClause wcl = (WLClause) obj;
            if (this.lits.length != wcl.lits.length) {
                return false;
            }
            boolean ok;
            for (int lit : this.lits) {
                ok = false;
                for (int lit2 : wcl.lits) {
                    if (lit == lit2) {
                        ok = true;
                        break;
                    }
                }
                if (!ok) {
                    return false;
                }
            }
            return true;
        } catch (ClassCastException e) {
            return false;
        }
    }

    @Override
    public int hashCode() {
        long sum = 0;
        for (int p : this.lits) {
            sum += p;
        }
        return (int) sum / this.lits.length;
    }

    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    public Constr toConstraint() {
        return this;
    }

    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        calcReason(p, outReason);
    }

    public boolean canBeSatisfiedByCountingLiterals() {
        return true;
    }

    public int requiredNumberOfSatisfiedLiterals() {
        return 1;
    }

    public boolean isSatisfied() {
        for (int p : this.lits) {
            if (voc.isSatisfied(p))
                return true;
        }
        return false;
    }

    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        for (int i = trail.size() - 1; i >= 0; i--) {
            if (var(trail.get(i)) == var(this.lits[0])) {
                return i;
            }
        }
        return -1;
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
