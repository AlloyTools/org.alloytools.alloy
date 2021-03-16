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

@Feature("constraint")
public final class LearntWLClause extends WLClause {

    public LearntWLClause(IVecInt ps, ILits voc) {
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
        if (this.lits.length == 0)
            return;
        assert this.lits.length > 1;
        // prendre un deuxieme litt???ral ??? surveiller
        int maxi = 1;
        int maxlevel = this.voc.getLevel(this.lits[1]);
        for (int i = 2; i < this.lits.length; i++) {
            int level = this.voc.getLevel(this.lits[i]);
            if (level > maxlevel) {
                maxi = i;
                maxlevel = level;
            }
        }
        int l = this.lits[1];
        this.lits[1] = this.lits[maxi];
        this.lits[maxi] = l;
        // add really the clause inside the solver
        this.voc.watch(this.lits[0] ^ 1, this);
        this.voc.watch(this.lits[1] ^ 1, this);

    }

    public boolean learnt() {
        return true;
    }

    public void setLearnt() {
        // do nothing
    }

    /**
     * @since 2.1
     */
    public void forwardActivity(double claInc) {

    }

    /**
     * @param claInc
     */
    public void incActivity(double claInc) {
        this.activity += claInc;
    }

    public boolean propagatePI(MandatoryLiteralListener s, int p) {
        this.voc.watch(p, this);
        return true;
    }
}
