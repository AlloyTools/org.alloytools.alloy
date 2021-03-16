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
package org.sat4j;

import org.sat4j.core.ASolverFactory;
import org.sat4j.minisat.constraints.MixedDataStructureDanielWL;
import org.sat4j.minisat.core.DataStructureFactory;
import org.sat4j.minisat.core.SearchParams;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.learning.MiniSATLearning;
import org.sat4j.minisat.orders.RSATPhaseSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.minisat.restarts.ArminRestarts;
import org.sat4j.specs.ISolver;

/**
 * That class is the entry point to the default, best performing configuration
 * of SAT4J. Since there is only one concrete reference per strategy used inside
 * the solver, it is a good start for people willing to reduce the library to
 * the minimal number of classes needed to run a SAT solver. The main method
 * allow to run the solver from the command line.
 * 
 * @author leberre
 * @since 2.2
 */
public class LightFactory extends ASolverFactory<ISolver> {
    private static final long serialVersionUID = 1460304168178023681L;
    private static LightFactory instance;

    private static synchronized void createInstance() {
        if (instance == null) {
            instance = new LightFactory();
        }
    }

    /**
     * Access to the single instance of the factory.
     * 
     * @return the singleton of that class.
     */
    public static LightFactory instance() {
        if (instance == null) {
            createInstance();
        }
        return instance;
    }

    @Override
    public ISolver defaultSolver() {
        MiniSATLearning<DataStructureFactory> learning = new MiniSATLearning<DataStructureFactory>();
        Solver<DataStructureFactory> solver = new Solver<DataStructureFactory>(
                learning, new MixedDataStructureDanielWL(), new VarOrderHeap(
                        new RSATPhaseSelectionStrategy()), new ArminRestarts());
        learning.setSolver(solver);
        solver.setSimplifier(solver.EXPENSIVE_SIMPLIFICATION);
        solver.setSearchParams(new SearchParams(1.1, 100));
        return solver;
    }

    @Override
    public ISolver lightSolver() {
        return defaultSolver();
    }

    public static void main(final String[] args) {
        AbstractLauncher lanceur = new BasicLauncher<ISolver>(
                LightFactory.instance());
        if (args.length != 1) {
            lanceur.usage();
            return;
        }
        lanceur.run(args);
        System.exit(lanceur.getExitCode().value());
    }

}
