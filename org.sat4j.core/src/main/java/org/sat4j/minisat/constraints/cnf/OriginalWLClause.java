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
import org.sat4j.minisat.core.ILits;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.UnitPropagationListener;

@Feature("constraint")
public final class OriginalWLClause extends WLClause {

    public OriginalWLClause(IVecInt ps, ILits voc) {
        super(ps, voc);
    }

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.constraints.cnf.WLClause#register()
     */
    public void register() {
        assert this.lits.length > 1;
        this.voc.watch(this.lits[0] ^ 1, this);
        this.voc.watch(this.lits[1] ^ 1, this);
    }

    public boolean learnt() {
        return false;
    }

    public void setLearnt() {
        // do nothing
    }

    /**
     * Creates a brand new clause, presumably from external data.
     * 
     * @param s
     *            the object responsible for unit propagation
     * @param voc
     *            the vocabulary
     * @param literals
     *            the literals to store in the clause
     * @return the created clause or null if the clause should be ignored
     *         (tautology for example)
     */
    public static OriginalWLClause brandNewClause(UnitPropagationListener s,
            ILits voc, IVecInt literals) {
        OriginalWLClause c = new OriginalWLClause(literals, voc);
        c.register();
        return c;
    }

    /**
     * @since 2.1
     */
    public void forwardActivity(double claInc) {
        this.activity += claInc;
    }

    /**
     * @param claInc
     */
    public void incActivity(double claInc) {

    }

    private int savedindex = 2;

    public boolean propagatePI(MandatoryLiteralListener s, int p) {
        final int[] mylits = this.lits;
        // Lits[1] must contain a falsified literal
        if (mylits[0] == (p ^ 1)) {
            mylits[0] = mylits[1];
            mylits[1] = p ^ 1;
        }
        // assert mylits[1] == (p ^ 1);
        int previous = p ^ 1;
        // look for a new satisfied literal to watch
        for (int i = savedindex; i < mylits.length; i++) {
            if (this.voc.isSatisfied(mylits[i])) {
                mylits[1] = mylits[i];
                mylits[i] = previous;
                this.voc.watch(mylits[1] ^ 1, this);
                savedindex = i + 1;
                return true;
            }
        }
        // the clause is now either unit
        this.voc.watch(p, this);
        // first literal is mandatory
        s.isMandatory(mylits[0]);
        return true;
    }

    @Override
    public boolean propagate(UnitPropagationListener s, int p) {
        this.savedindex = 2;
        return super.propagate(s, p);
    }

}
