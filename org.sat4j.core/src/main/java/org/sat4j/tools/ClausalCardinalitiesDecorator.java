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

import org.sat4j.annotations.Feature;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.tools.encoding.EncodingStrategyAdapter;
import org.sat4j.tools.encoding.Policy;

/**
 * 
 * A decorator for clausal cardinalities constraints.
 * 
 * @author stephanieroussel
 * @since 2.3.1
 * @param <T>
 */
@Feature("solver")
public class ClausalCardinalitiesDecorator<T extends ISolver>
        extends SolverDecorator<T> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final EncodingStrategyAdapter encodingAdapter;

    public ClausalCardinalitiesDecorator(T solver) {
        super(solver);
        this.encodingAdapter = new Policy();
    }

    public ClausalCardinalitiesDecorator(T solver,
            EncodingStrategyAdapter encodingAd) {
        super(solver);
        this.encodingAdapter = encodingAd;
    }

    @Override
    public IConstr addAtLeast(IVecInt literals, int k)
            throws ContradictionException {
        if (k == 1) {
            return this.encodingAdapter.addAtLeastOne(decorated(), literals);
        } else {
            return this.encodingAdapter.addAtLeast(decorated(), literals, k);
        }
    }

    @Override
    public IConstr addAtMost(IVecInt literals, int k)
            throws ContradictionException {
        if (k == 1) {
            return this.encodingAdapter.addAtMostOne(decorated(), literals);
        } else {
            return this.encodingAdapter.addAtMost(decorated(), literals, k);
        }
    }

    @Override
    public IConstr addExactly(IVecInt literals, int k)
            throws ContradictionException {

        if (k == 1) {
            return this.encodingAdapter.addExactlyOne(decorated(), literals);
        } else {
            return this.encodingAdapter.addExactly(decorated(), literals, k);
        }
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String prefix) {
        return super.toString(prefix) + "\n" + "Cardinality to SAT encoding: \n"
                + "Encoding: " + this.encodingAdapter + "\n";
    }

}
