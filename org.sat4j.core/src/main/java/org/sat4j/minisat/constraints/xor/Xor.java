package org.sat4j.minisat.constraints.xor;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.ILits;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

/**
 * A simple implementation of a xor constraint to be handled in Sat4j CDCL
 * solver.
 * 
 * As for each constraint in the solver, the propagation and conflict analysis
 * is performed locally for each constraint, not globally like in the SMT
 * framework.
 * 
 * As such, the constraint uses an extended form of watched literals, basic
 * analysis in case of conflicts (it will typically return a clause of the CNF
 * encoding), so think about that implementation as a lazy clause generation of
 * the full CNF encoding.
 *
 * The normalized for of the constraint is:
 * 
 * v1 xor v2 xor v3 xor ... xor vn = (true | false)
 * 
 * where v1 are dimacs positive literals (using Sat4j internal representation)
 * 
 * if rhs is false, then an even number of literals must be satisfied, else an
 * odd number of literals must be satisfied (thus the name parity constraints).
 * 
 * @author leberre
 * @since 2.3.6
 */
@Feature("constraint")
public class Xor implements Constr, Propagatable {

    private final int[] lits;
    private final boolean parity;
    private final ILits voc;

    public static Xor createParityConstraint(IVecInt lits, boolean parity,
            ILits voc) {
        // TODO ensure normal form
        Xor xor = new Xor(lits, parity, voc);
        xor.register();
        return xor;
    }

    public Xor(IVecInt lits, boolean parity, ILits voc) {
        this.lits = new int[lits.size()];
        lits.copyTo(this.lits);
        this.parity = parity;
        this.voc = voc;
    }

    @Override
    public boolean learnt() {
        return false;
    }

    @Override
    public int size() {
        return lits.length;
    }

    @Override
    public int get(int i) {
        return lits[i];
    }

    @Override
    public double getActivity() {
        // TODO: implement this method !
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    @Override
    public String toString(VarMapper mapper) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean propagate(UnitPropagationListener s, int p) {
        // we use the same trick as for clauses: we move the variables inside
        // the constraint
        // to keep the two doubly watched literals in front of the constraints
        int tmp, nbSatisfied = 0;
        if (p == lits[0] || LiteralsUtils.neg(p) == lits[0]) {
            tmp = lits[1];
            lits[1] = lits[0];
            lits[0] = tmp;
        }
        if (this.voc.isSatisfied(lits[1])) {
            nbSatisfied = 1;
        }
        // look for new literal to watch and counting satisfied literals
        for (int i = 2; i < lits.length; i++) {
            if (this.voc.isSatisfied(lits[i])) {
                nbSatisfied++;
            } else if (this.voc.isUnassigned(lits[i])) {
                tmp = lits[1];
                lits[1] = lits[i];
                lits[i] = tmp;
                this.voc.watch(lits[1] ^ 1, this);
                this.voc.watch(lits[1], this);
                this.voc.watches(p ^ 1).remove(this);
                return true;
            }
        }
        this.voc.watch(p, this);
        // propagates first watched literal, depending on the number of
        // satisfied literals
        int toPropagate = ((nbSatisfied & 1) == 1) == parity ? lits[0]
                : LiteralsUtils.neg(lits[0]);
        return s.enqueue(toPropagate, this);
    }

    @Override
    public boolean propagatePI(MandatoryLiteralListener l, int p) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public Constr toConstraint() {
        return this;
    }

    @Override
    public void remove(UnitPropagationListener upl) {
        this.voc.watches(this.lits[0]).remove(this);
        this.voc.watches(this.lits[0] ^ 1).remove(this);
        this.voc.watches(this.lits[1]).remove(this);
        this.voc.watches(this.lits[1] ^ 1).remove(this);
    }

    @Override
    public boolean simplify() {
        return false;
    }

    @Override
    public void calcReason(int p, IVecInt outReason) {
        int nbUnassigned = 0;
        for (int i = 0; i < lits.length; i++) {
            if (this.voc.isFalsified(lits[i])) {
                outReason.push(lits[i] ^ 1);
            } else if (this.voc.isSatisfied(lits[i])) {
                outReason.push(lits[i]);
            } else {
                nbUnassigned++;
            }
        }
        assert nbUnassigned == (p == ILits.UNDEFINED ? 0 : 1);
    }

    @Override
    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void incActivity(double claInc) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void forwardActivity(double claInc) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean locked() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void setLearnt() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void register() {
        this.voc.watch(this.lits[0], this);
        this.voc.watch(this.lits[0] ^ 1, this);
        this.voc.watch(this.lits[1], this);
        this.voc.watch(this.lits[1] ^ 1, this);
    }

    @Override
    public void rescaleBy(double d) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void setActivity(double d) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void assertConstraint(UnitPropagationListener s) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean canBeSatisfiedByCountingLiterals() {
        return true;
    }

    @Override
    public int requiredNumberOfSatisfiedLiterals() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public boolean isSatisfied() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public String dump() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        for (int l : lits) {
            stb.append(LiteralsUtils.toDimacs(l));
            stb.append(" ");
            stb.append(voc.isUnassigned(l) ? "U"
                    : (voc.isFalsified(l) ? "F" : "T"));
            stb.append(" x ");
        }
        stb.append(parity);
        return stb.toString();
    }

    /**
     * Activates this Xor constraint.
     */
    public void activate() {
        this.register();
    }

    /**
     * Deactivates (i.e., forgets) a constraint, as there is no easy way to use
     * selectors with parity constraints.
     */
    public void deactivate() {
        this.remove(null);
    }

}
