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

import static org.sat4j.core.LiteralsUtils.neg;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.ILits;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.MandatoryLiteralListener;
import org.sat4j.specs.UnitPropagationListener;

/**
 * @since 2.1
 */
@Feature("constraint")
public class OriginalHTClause extends HTClause {

    public OriginalHTClause(IVecInt ps, ILits voc) {
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
        this.voc.watch(neg(this.head), this);
        this.voc.watch(neg(this.tail), this);
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
    public static OriginalHTClause brandNewClause(UnitPropagationListener s,
            ILits voc, IVecInt literals) {
        OriginalHTClause c = new OriginalHTClause(literals, voc);
        c.register();
        return c;
    }

    public void forwardActivity(double claInc) {
        this.activity += claInc;
    }

    /**
     * @param claInc
     */
    public void incActivity(double claInc) {

    }

    public void setActivity(double claInc) {
        // do nothing
    }

    public boolean propagatePI(MandatoryLiteralListener l, int p) {
        if (this.head == neg(p)) {
            final int[] mylits = this.middleLits;
            // moving head on the right
            while (savedindexhead < mylits.length
                    && this.voc.isFalsified(mylits[savedindexhead])) {
                savedindexhead++;
            }
            assert savedindexhead <= mylits.length;
            if (savedindexhead == mylits.length) {
                l.isMandatory(this.tail);
            } else {
                this.head = mylits[savedindexhead];
                mylits[savedindexhead] = neg(p);
                this.voc.watch(neg(this.head), this);
            }
        } else {
            assert this.tail == neg(p);
            final int[] mylits = this.middleLits;
            // moving tail on the left
            while (savedindextail >= 0
                    && this.voc.isFalsified(mylits[savedindextail])) {
                savedindextail--;
            }
            assert -1 <= savedindextail;
            if (-1 == savedindextail) {
                l.isMandatory(this.head);
            } else {
                this.tail = mylits[savedindextail];
                mylits[savedindextail] = neg(p);
                this.voc.watch(neg(this.tail), this);
            }
        }
        return true;
    }

    private int savedindexhead;
    private int savedindextail;

    @Override
    public boolean propagate(UnitPropagationListener s, int p) {
        this.savedindexhead = 0;
        this.savedindextail = middleLits.length - 1;
        return super.propagate(s, p);
    }
}
