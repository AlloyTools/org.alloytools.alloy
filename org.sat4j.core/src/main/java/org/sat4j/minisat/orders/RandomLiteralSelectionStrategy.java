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
package org.sat4j.minisat.orders;

import static org.sat4j.core.LiteralsUtils.negLit;
import static org.sat4j.core.LiteralsUtils.posLit;

import java.util.Random;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;

/**
 * The variable selection strategy randomly picks one phase, either positive or
 * negative.
 * 
 * @author leberre
 * 
 */
@Feature(value = "phaseheuristics", parent = "expert")
public final class RandomLiteralSelectionStrategy
        implements IPhaseSelectionStrategy {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * @since 2.2
     */
    public static final Random RAND = System
            .getProperty("NONDETERMINISTIC") == null ? new Random(123456789)
                    : new Random();

    public void assignLiteral(int p) {
    }

    public void init(int nlength) {
    }

    public void init(int var, int p) {
    }

    public int select(int var) {
        if (RAND.nextBoolean()) {
            return posLit(var);
        }
        return negLit(var);
    }

    public void updateVar(int p) {
    }

    public void updateVarAtDecisionLevel(int q) {
    }

    @Override
    public String toString() {
        return "random phase selection";
    }
}
