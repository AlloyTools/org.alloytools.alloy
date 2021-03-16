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
package org.sat4j.minisat.constraints.card;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.constraints.cnf.Lits;
import org.sat4j.minisat.constraints.cnf.UnitClauses;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Undoable;
import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

@Feature("constraint")
public class MinWatchCard
        implements Propagatable, Constr, Undoable, Serializable {

    private static final long serialVersionUID = 1L;

    public static final boolean ATLEAST = true;

    public static final boolean ATMOST = false;

    /**
     * degree of the cardinality constraint
     */
    protected int degree;

    /**
     * literals involved in the constraint
     */
    protected final int[] lits;

    /**
     * contains the sign of the constraint : ATLEAT or ATMOST
     */
    private boolean moreThan;

    /**
     * contains the sum of the coefficients of the watched literals
     */
    protected int watchCumul;

    /**
     * Vocabulary of the constraint
     */
    private final ILits voc;

    /**
     * Maximum number of falsified literal in the constraint.
     * 
     */
    protected final int maxUnsatisfied;

    /**
     * Constructs and normalizes a cardinality constraint. used by
     * minWatchCardNew in the non-normalized case.
     * 
     * @param voc
     *            vocabulary used by the constraint
     * @param ps
     *            literals involved in the constraint
     * @param moreThan
     *            should be ATLEAST or ATMOST;
     * @param degree
     *            degree of the constraint
     */
    public MinWatchCard(ILits voc, IVecInt ps, boolean moreThan, int degree) {
        // On met en place les valeurs
        this.voc = voc;
        this.degree = degree;
        this.moreThan = moreThan;

        // On simplifie ps
        int[] index = new int[voc.nVars() * 2 + 2];
        // Fresh array should have all elements set to 0

        // On repertorie les litt?raux utiles
        for (int i = 0; i < ps.size(); i++) {
            int p = ps.get(i);
            if (index[p ^ 1] == 0) {
                index[p]++;
            } else {
                index[p ^ 1]--;
            }
        }
        // On supprime les litt?raux inutiles
        int ind = 0;
        while (ind < ps.size()) {
            if (index[ps.get(ind)] > 0) {
                index[ps.get(ind)]--;
                ind++;
            } else {
                // ??
                if ((ps.get(ind) & 1) != 0) {
                    this.degree--;
                }
                ps.delete(ind);
            }
        }

        // On copie les litt?raux de la contrainte
        this.lits = new int[ps.size()];
        ps.moveTo(this.lits);

        // On normalise la contrainte au sens de Barth
        normalize();
        this.maxUnsatisfied = lits.length - this.degree;
    }

    /**
     * Constructs and normalizes a cardinality constraint. used by
     * MinWatchCardPB.normalizedMinWatchCardNew() in the normalized case.
     * 
     * <strong>Should not be used if parameters are not already
     * normalized</strong> This constraint is always an ATLEAST constraint.
     * 
     * @param voc
     *            vocabulary used by the constraint
     * @param ps
     *            literals involved in the constraint
     * @param degree
     *            degree of the constraint
     */
    protected MinWatchCard(ILits voc, IVecInt ps, int degree) {
        // On met en place les valeurs
        this.voc = voc;
        this.degree = degree;
        this.moreThan = ATLEAST;

        // On copie les litt?raux de la contrainte
        this.lits = new int[ps.size()];
        ps.moveTo(this.lits);
        this.maxUnsatisfied = lits.length - this.degree;
    }

    /**
     * computes the reason for a literal
     * 
     * @param p
     *            falsified literal (or Lit.UNDEFINED)
     * @param outReason
     *            the reason to be computed. Vector of literals.
     * @see Constr#calcReason(int p, IVecInt outReason)
     */
    public void calcReason(int p, IVecInt outReason) {
        int c = p == ILits.UNDEFINED ? -1 : 0;
        for (int q : this.lits) {
            if (this.voc.isFalsified(q)) {
                outReason.push(q ^ 1);
                if (++c >= this.maxUnsatisfied) {
                    return;
                }
            }
        }
    }

    /**
     * Returns the activity of the constraint
     * 
     * @return activity value of the constraint
     * @see Constr#getActivity()
     */
    public double getActivity() {
        return 0;
    }

    /**
     * Increments activity of the constraint
     * 
     * @param claInc
     *            value to be added to the activity of the constraint
     * @see Constr#incActivity(double claInc)
     */
    public void incActivity(double claInc) {
    }

    public void setActivity(double d) {
    }

    /**
     * Returns wether the constraint is learnt or not.
     * 
     * @return false : a MinWatchCard cannot be learnt.
     * @see Constr#learnt()
     */
    public boolean learnt() {
        return false;
    }

    /**
     * Simplifies the constraint w.r.t. the assignments of the literals
     * 
     * @param voc
     *            vocabulary used
     * @param ps
     *            literals involved
     * @return value to be added to the degree. This value is less than or equal
     *         to 0.
     */
    protected static int linearisation(ILits voc, IVecInt ps) {
        // Stockage de l'influence des modifications
        int modif = 0;

        for (int i = 0; i < ps.size();) {
            // on verifie si le litteral est affecte
            if (voc.isUnassigned(ps.get(i))) {
                i++;
            } else {
                // Si le litteral est satisfait,
                // ?a revient ? baisser le degr?
                if (voc.isSatisfied(ps.get(i))) {
                    modif--;
                }
                // dans tous les cas, s'il est assign?,
                // on enleve le ieme litteral
                ps.set(i, ps.last());
                ps.pop();
            }
        }

        assert modif <= 0;

        return modif;
    }

    /**
     * Returns if the constraint is the reason for a unit propagation.
     * 
     * @return true
     * @see Constr#locked()
     */
    public boolean locked() {
        return true;
    }

    /**
     * Constructs a cardinality constraint with a minimal set of watched
     * literals Permet la cr?ation de contrainte de cardinalit? ? observation
     * minimale
     * 
     * @param s
     *            tool for propagation
     * @param voc
     *            vocalulary used by the constraint
     * @param ps
     *            literals involved in the constraint
     * @param moreThan
     *            sign of the constraint. Should be ATLEAST or ATMOST.
     * @param degree
     *            degree of the constraint
     * @return a new cardinality constraint, null if it is a tautology
     * @throws ContradictionException
     */
    public static Constr minWatchCardNew(UnitPropagationListener s, ILits voc,
            IVecInt ps, boolean moreThan, int degree)
            throws ContradictionException {

        int mydegree = degree + linearisation(voc, ps);

        if (ps.size() < mydegree) {
            throw new ContradictionException();
        } else if (ps.size() == mydegree) {
            for (int i = 0; i < ps.size(); i++) {
                if (!s.enqueue(ps.get(i))) {
                    throw new ContradictionException();
                }
            }
            return new UnitClauses(ps);
        }

        // La contrainte est maintenant cr??e
        MinWatchCard retour = new MinWatchCard(voc, ps, moreThan, mydegree);

        if (retour.degree <= 0) {
            return null;
        }

        retour.computeWatches();

        retour.computePropagation(s);

        return retour;
    }

    /**
     * normalize the constraint (cf. P.Barth normalization)
     */
    public final void normalize() {
        // Gestion du signe
        if (!this.moreThan) {
            // On multiplie le degr? par -1
            this.degree = 0 - this.degree;
            // On r?vise chaque litt?ral
            for (int indLit = 0; indLit < this.lits.length; indLit++) {
                this.lits[indLit] = this.lits[indLit] ^ 1;
                this.degree++;
            }
            this.moreThan = true;
        }
    }

    /**
     * propagates the value of a falsified literal
     * 
     * @param s
     *            tool for literal propagation
     * @param p
     *            falsified literal
     * @return false if an inconistency is detected, else true
     */
    public boolean propagate(UnitPropagationListener s, int p) {
        this.savedindex = this.degree + 1;
        // Si la contrainte est responsable de propagation unitaire
        if (this.watchCumul == this.degree) {
            this.voc.watch(p, this);
            return false;
        }

        // Recherche du litt?ral falsifi?
        int indFalsified = 0;
        while ((this.lits[indFalsified] ^ 1) != p) {
            indFalsified++;
        }
        assert this.watchCumul > this.degree;

        // Recherche du litt?ral swap
        int indSwap = this.degree + 1;
        while (indSwap < this.lits.length
                && this.voc.isFalsified(this.lits[indSwap])) {
            indSwap++;
        }

        // Mise ? jour de la contrainte
        if (indSwap == this.lits.length) {
            // Si aucun litt?ral n'a ?t? trouv?
            this.voc.watch(p, this);
            // La limite est atteinte
            this.watchCumul--;
            assert this.watchCumul == this.degree;
            this.voc.undos(p).push(this);

            // On met en queue les litt?raux impliqu?s
            for (int i = 0; i <= this.degree; i++) {
                if (p != (this.lits[i] ^ 1) && !s.enqueue(this.lits[i], this)) {
                    return false;
                }
            }

            return true;
        }
        // Si un litt?ral a ?t? trouv? on les ?change
        int tmpInt = this.lits[indSwap];
        this.lits[indSwap] = this.lits[indFalsified];
        this.lits[indFalsified] = tmpInt;

        // On observe le nouveau litt?ral
        this.voc.watch(tmpInt ^ 1, this);

        return true;
    }

    /**
     * Removes a constraint from the solver
     * 
     * @since 2.1
     */
    public void remove(UnitPropagationListener upl) {
        for (int i = 0; i < Math.min(this.degree + 1, this.lits.length); i++) {
            this.voc.watches(this.lits[i] ^ 1).remove(this);
        }
    }

    /**
     * Rescales the activity value of the constraint
     * 
     * @param d
     *            rescale factor
     */
    public void rescaleBy(double d) {
        // TODO rescaleBy
    }

    /**
     * simplifies the constraint
     * 
     * @return true if the constraint is satisfied, else false
     */
    public boolean simplify() {
        // Calcul de la valeur actuelle
        for (int i = 0, count = 0; i < this.lits.length; i++) {
            if (this.voc.isSatisfied(this.lits[i]) && ++count == this.degree) {
                return true;
            }
        }

        return false;
    }

    /**
     * Returns a string representation of the constraint.
     * 
     * @return representation of the constraint.
     */
    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        // stb.append("Card (" + this.lits.length + ") : ");
        if (this.lits.length > 0) {
            // if (voc.isUnassigned(lits[0])) {
            stb.append(Lits.toStringX(this.lits[0]));
            stb.append("[");
            stb.append(this.voc.valueToString(this.lits[0]));
            // stb.append("@");
            // stb.append(this.voc.getLevel(this.lits[0]));
            stb.append("]");
            stb.append(" "); //$NON-NLS-1$
            // }
            for (int i = 1; i < this.lits.length; i++) {
                // if (voc.isUnassigned(lits[i])) {
                // stb.append(" + "); //$NON-NLS-1$
                stb.append(Lits.toStringX(this.lits[i]));
                stb.append("[");
                stb.append(this.voc.valueToString(this.lits[i]));
                // stb.append("@");
                // stb.append(this.voc.getLevel(this.lits[i]));
                stb.append("]");
                stb.append(" "); //$NON-NLS-1$
                // }
            }
            stb.append(">= "); //$NON-NLS-1$
            stb.append(this.degree);
        }
        return stb.toString();
    }

    /**
     * Updates information on the constraint in case of a backtrack
     * 
     * @param p
     *            unassigned literal
     */
    public void undo(int p) {
        // Le litt?ral observ? et falsifi? devient non assign?
        this.watchCumul++;
    }

    public void setLearnt() {
        throw new UnsupportedOperationException();
    }

    public void register() {
        computeWatches();
    }

    public int size() {
        return this.lits.length;
    }

    public int get(int i) {
        return this.lits[i];
    }

    public void assertConstraint(UnitPropagationListener s) {
        boolean ret = true;
        for (Integer lit : this.lits) {
            if (this.voc.isUnassigned(lit)) {
                ret &= s.enqueue(lit, this);
            }
        }
        assert ret == true;
    }

    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        if (this.watchCumul == this.degree) {
            for (int i = 0; i < this.watchCumul; i++) {
                s.enqueue(this.lits[i]);
            }
        }
    }

    protected void computeWatches() {
        int indSwap = this.lits.length;
        int tmpInt;
        for (int i = 0; i <= this.degree && i < indSwap; i++) {
            while (this.voc.isFalsified(this.lits[i]) && --indSwap > i) {
                tmpInt = this.lits[i];
                this.lits[i] = this.lits[indSwap];
                this.lits[indSwap] = tmpInt;
            }

            // Si le litteral est observable
            if (!this.voc.isFalsified(this.lits[i])) {
                this.watchCumul++;
                this.voc.watch(this.lits[i] ^ 1, this);
            }
        }
        if (this.watchCumul <= this.degree) {
            // chercher tous les litteraux a regarder
            // par ordre de niveau decroissant
            int free = 1;
            while (this.watchCumul <= this.degree && free > 0) {
                free = 0;
                // regarder le litteral falsifie au plus bas niveau
                int maxlevel = -1, maxi = -1;
                for (int i = this.watchCumul; i < this.lits.length; i++) {
                    if (this.voc.isFalsified(this.lits[i])) {
                        free++;
                        int level = this.voc.getLevel(this.lits[i]);
                        if (level > maxlevel) {
                            maxi = i;
                            maxlevel = level;
                        }
                    }
                }
                if (free > 0) {
                    assert maxi >= 0;
                    this.voc.watch(this.lits[maxi] ^ 1, this);
                    tmpInt = this.lits[maxi];
                    this.lits[maxi] = this.lits[this.watchCumul];
                    this.lits[this.watchCumul] = tmpInt;
                    this.watchCumul++;
                    free--;
                    assert free >= 0;
                }
            }
            assert this.lits.length == 1 || this.watchCumul > 1;
        }

    }

    protected MinWatchCard computePropagation(UnitPropagationListener s)
            throws ContradictionException {

        // Si on a des litteraux impliques
        if (this.watchCumul == this.degree) {
            for (int i = 0; i < this.lits.length; i++) {
                if (!s.enqueue(this.lits[i])) {
                    throw new ContradictionException();
                }
            }
            return null;
        }

        // Si on n'observe pas suffisamment
        if (this.watchCumul < this.degree) {
            throw new ContradictionException();
        }
        return this;
    }

    public int[] getLits() {
        int[] tmp = new int[size()];
        System.arraycopy(this.lits, 0, tmp, 0, size());
        return tmp;
    }

    public ILits getVocabulary() {
        return this.voc;
    }

    @Override
    public boolean equals(Object card) {
        if (card == null) {
            return false;
        }
        if (this.getClass() != card.getClass()) {
            return false;
        }
        try {
            MinWatchCard mcard = (MinWatchCard) card;
            if (mcard.degree != this.degree) {
                return false;
            }
            if (this.lits.length != mcard.lits.length) {
                return false;
            }
            boolean ok;
            for (int lit : this.lits) {
                ok = false;
                for (int lit2 : mcard.lits) {
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
        sum += this.degree;
        return (int) sum / (this.lits.length + 1);
    }

    /**
     * @since 2.1
     */
    public void forwardActivity(double claInc) {
        // do nothing
    }

    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    public Constr toConstraint() {
        return this;
    }

    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        int bound = p == ILits.UNDEFINED ? this.watchCumul
                : this.watchCumul - 1;
        for (int i = 0; i < bound; i++) {
            int q = lits[i];
            assert voc.isFalsified(q);
            outReason.push(q ^ 1);
        }
    }

    private int savedindex = this.degree + 1;

    public boolean propagatePI(MandatoryLiteralListener l, int p) {
        // Recherche du litt?ral falsifi?
        int indFalsified = 0;
        while ((this.lits[indFalsified] ^ 1) != p) {
            indFalsified++;
        }
        assert this.watchCumul >= this.degree;

        // Recherche du litt?ral swap
        int indSwap = this.savedindex;
        while (indSwap < this.lits.length
                && this.voc.isFalsified(this.lits[indSwap])) {
            indSwap++;
        }

        // Mise ? jour de la contrainte
        if (indSwap == this.lits.length) {
            // Si aucun litt?ral n'a ?t? trouv?
            this.voc.watch(p, this);

            // On met en queue les litt?raux impliqu?s
            for (int i = 0; i <= this.degree; i++) {
                if (p != (this.lits[i] ^ 1)) {
                    l.isMandatory(this.lits[i]);
                }
            }
            return true;
        }
        this.savedindex = indSwap + 1;
        // Si un litt?ral a ?t? trouv? on les ?change
        int tmpInt = this.lits[indSwap];
        this.lits[indSwap] = this.lits[indFalsified];
        this.lits[indFalsified] = tmpInt;

        // On observe le nouveau litt?ral
        this.voc.watch(tmpInt ^ 1, this);

        return true;

    }

    public boolean canBeSatisfiedByCountingLiterals() {
        return true;
    }

    public int requiredNumberOfSatisfiedLiterals() {
        return degree;
    }

    public boolean isSatisfied() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        int nUnsat = 0;
        Set<Integer> litsSet = new HashSet<Integer>();
        for (Integer i : this.lits)
            litsSet.add(i);
        for (int i = 0; i < trail.size(); ++i) {
            if (litsSet.contains(trail.get(i) ^ 1)) {
                ++nUnsat;
                if (nUnsat == this.maxUnsatisfied)
                    return i;
            }
        }
        return -1;
    }

    public String toString(VarMapper mapper) {
        if (mapper == null) {
            return toString();
        }
        StringBuilder stb = new StringBuilder();
        // stb.append("Card (" + this.lits.length + ") : ");
        if (this.lits.length > 0) {
            // if (voc.isUnassigned(lits[0])) {
            stb.append(mapper.map(LiteralsUtils.toDimacs(this.lits[0])));
            stb.append("[");
            stb.append(this.voc.valueToString(this.lits[0]));
            // stb.append("@");
            // stb.append(this.voc.getLevel(this.lits[0]));
            stb.append("]");
            stb.append(" "); //$NON-NLS-1$
            // }
            for (int i = 1; i < this.lits.length; i++) {
                // if (voc.isUnassigned(lits[i])) {
                // stb.append(" + "); //$NON-NLS-1$
                stb.append(mapper.map(LiteralsUtils.toDimacs(this.lits[i])));
                stb.append("[");
                stb.append(this.voc.valueToString(this.lits[i]));
                // stb.append("@");
                // stb.append(this.voc.getLevel(this.lits[i]));
                stb.append("]");
                stb.append(" "); //$NON-NLS-1$
                // }
            }
            stb.append(">= "); //$NON-NLS-1$
            stb.append(this.degree);
        }
        return stb.toString();
    }

    @Override
    public String dump() {
        StringBuilder stb = new StringBuilder();
        stb.append(LiteralsUtils.toOPB(this.lits[0]));
        int i = 1;
        while (i < this.lits.length) {
            stb.append(" + "); //$NON-NLS-1$
            stb.append(LiteralsUtils.toOPB(lits[i++]));
        }
        stb.append(" >= "); //$NON-NLS-1$
        stb.append(this.degree);

        return stb.toString();
    }
}
