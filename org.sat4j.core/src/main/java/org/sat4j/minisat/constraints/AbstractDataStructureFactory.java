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
package org.sat4j.minisat.constraints;

import java.io.Serializable;

import org.sat4j.core.Vec;
import org.sat4j.minisat.core.DataStructureFactory;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Learner;
import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;

/**
 * @author leberre To change the template for this generated type comment go to
 *         Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public abstract class AbstractDataStructureFactory implements
        DataStructureFactory, Serializable {

    /**
	 * 
	 */
    private static final long serialVersionUID = 1L;

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.sat4j.minisat.core.DataStructureFactory#conflictDetectedInWatchesFor
     * (int)
     */
    public void conflictDetectedInWatchesFor(int p, int i) {
        for (int j = i + 1; j < this.tmp.size(); j++) {
            this.lits.watch(p, this.tmp.get(j));
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.core.DataStructureFactory#getWatchesFor(int)
     */
    public IVec<Propagatable> getWatchesFor(int p) {
        this.tmp.clear();
        this.lits.watches(p).moveTo(this.tmp);
        return this.tmp;
    }

    protected ILits lits;

    protected AbstractDataStructureFactory() {
        this.lits = createLits();
    }

    protected abstract ILits createLits();

    private final IVec<Propagatable> tmp = new Vec<Propagatable>();

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.DataStructureFactory#createVocabulary()
     */
    public ILits getVocabulary() {
        return this.lits;
    }

    protected UnitPropagationListener solver;

    protected Learner learner;

    public void setUnitPropagationListener(UnitPropagationListener s) {
        this.solver = s;
    }

    public void setLearner(Learner learner) {
        this.learner = learner;
    }

    public void reset() {
    }

    public void learnConstraint(Constr constr) {
        this.learner.learn(constr);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.sat4j.minisat.core.DataStructureFactory#createCardinalityConstraint
     * (org.sat4j.specs.VecInt, int)
     */
    public Constr createCardinalityConstraint(IVecInt literals, int degree)
            throws ContradictionException {
        throw new UnsupportedOperationException();
    }

    public Constr createUnregisteredCardinalityConstraint(IVecInt literals,
            int degree) {
        throw new UnsupportedOperationException();
    }
}
