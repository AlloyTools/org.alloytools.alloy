/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2019 Artois University and CNRS
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

package org.sat4j.tools.counting;

import java.util.Random;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.constraints.xor.Xor;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * This class allows to generate and manage random parity constraints for the
 * ApproxMC algorithm.
 * 
 * @author Romain Wallon
 */
public class ParityConstraintGenerator {

    /**
     * The pseudo-random number generator used to create random parity
     * constraints. This differs from the original paper, which uses numbers
     * generated from <a href="http://fourmilab.ch/hotbits/">HotBits</a>.
     */
    private static final Random RANDOM = System
            .getProperty("NONDETERMINISTIC") == null ? new Random(123456789)
                    : new Random();

    /**
     * The solver in which parity constraints are added.
     */
    private final ISolver solver;

    /**
     * The set of variables to consider for the parity constraints.
     */
    private final SamplingSet samplingSet;

    /**
     * The parity constraints that have been added to the solver.
     */
    private final ConstrGroup parityConstraints;

    /**
     * Whether the parity constraints are currently activated.
     */
    private boolean activated;

    /**
     * Creates a new ParityConstraintGenerator.
     * 
     * @param solver
     *            The solver in which parity constraints are added.
     * @param samplingSet
     *            The set of variables to consider in the parity constraints.
     */
    public ParityConstraintGenerator(ISolver solver, SamplingSet samplingSet) {
        this.solver = solver;
        this.samplingSet = samplingSet;
        this.parityConstraints = new ConstrGroup();
    }

    /**
     * Gives the number of constraints that are managed by this generator.
     * 
     * @return The number of constraints.
     */
    public int nbConstraints() {
        return parityConstraints.size();
    }

    /**
     * Generates {@code nb} parity constraints, and adds them to the solver. The
     * constraints are all activated.
     * 
     * @param nb
     *            The number of constraints to generate.
     */
    public void generate(int nb) {
        for (int i = 0; i < nb; i++) {
            // Looking for the variables to put in the constraint.
            IVecInt lits = new VecInt();
            for (IteratorInt it = samplingSet.variables(); it.hasNext();) {
                int var = it.next();
                if (RANDOM.nextBoolean()) {
                    lits.push(var);
                }
            }

            // Adding the generated constraint.
            // The parity is also randomly chosen.
            IConstr constr = solver.addParity(lits, RANDOM.nextBoolean());
            parityConstraints.add(constr);
        }

        // All added constraints are activated.
        activated = true;
    }

    /**
     * Gives the {@code i}-th parity constraint managed by this generator.
     * 
     * @param i
     *            The index of the constraint to get.
     * 
     * @return The {@code i}-th constraint.
     */
    public Xor getConstraint(int i) {
        assert i < nbConstraints();
        return (Xor) parityConstraints.getConstr(i);
    }

    /**
     * Deactivates all the constraints that have been generated. They are
     * <b>not</b> removed from the solver.
     */
    public void deactivate() {
        deactivate(nbConstraints());
    }

    /**
     * Deactivates the first {@code nb} constraints that have been generated.
     * They are <b>not</b> removed from the solver.
     * 
     * @param nb
     *            The number of constraints to deactivate
     */
    public void deactivate(int nb) {
        // Deactivating the constraints.
        for (int i = 0; i < nb; i++) {
            getConstraint(i).deactivate();
        }
        activated = false;

        // The learnt clauses cannot be kept as the input has changed.
        solver.clearLearntClauses();
    }

    /**
     * Activates all the constraints that have been generated.
     */
    public void activate() {
        activate(nbConstraints());
    }

    /**
     * Activates the first {@code nb} constraints that have been generated.
     * 
     * @param nb
     *            The number of constraints to activate
     */
    public void activate(int nb) {
        for (int i = 0; i < nb; i++) {
            getConstraint(i).activate();
        }
        activated = true;
    }

    /**
     * Clears the generated constraints from the solver.
     */
    public void clear() {
        // The constraints need to be activated before being removed.
        // Otherwise, an exception will be thrown.
        if (!activated) {
            activate();
        }

        // Actually removing the constraints.
        parityConstraints.removeFrom(solver);
        parityConstraints.clear();
    }

}
