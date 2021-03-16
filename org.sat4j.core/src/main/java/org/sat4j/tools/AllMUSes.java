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

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.sat4j.core.ASolverFactory;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * This is a tool for computing all the MUSes (Minimum Unsatisfiable Sets) of a
 * set of clauses.
 * 
 * @author sroussel
 * @since 2.3.3
 */
public class AllMUSes {

    private final AbstractClauseSelectorSolver<? extends ISolver> css;
    private final List<IVecInt> mssList;
    private final List<IVecInt> secondPhaseClauses;
    private final List<IVecInt> musList;
    private final ASolverFactory<? extends ISolver> factory;

    public AllMUSes(boolean group, ASolverFactory<? extends ISolver> factory) {
        this(group
                ? new GroupClauseSelectorSolver<ISolver>(
                        factory.defaultSolver())
                : new FullClauseSelectorSolver<ISolver>(factory.defaultSolver(),
                        false),
                factory);
    }

    public AllMUSes(ASolverFactory<? extends ISolver> factory) {
        this(false, factory);
    }

    public AllMUSes(AbstractClauseSelectorSolver<? extends ISolver> css,
            ASolverFactory<? extends ISolver> factory) {
        this.css = css;
        this.factory = factory;
        this.mssList = new ArrayList<IVecInt>();
        this.musList = new ArrayList<IVecInt>();
        this.secondPhaseClauses = new ArrayList<IVecInt>();
    }

    /**
     * Gets an instance of ISolver that can be used to compute all MUSes
     * 
     * @return the instance of ISolver to which the clauses will be added
     */
    public <T extends ISolver> T getSolverInstance() {
        return (T) this.css;
    }

    public List<IVecInt> computeAllMUSes() {
        return computeAllMUSes(VecInt.EMPTY);
    }

    /**
     * Reset the state of the object to allow computing new MUSes or MSSes.
     */
    public void reset() {
        this.secondPhaseClauses.clear();
    }

    public List<IVecInt> computeAllMUSes(SolutionFoundListener listener) {
        return computeAllMUSes(VecInt.EMPTY, listener);
    }

    public List<IVecInt> computeAllMUSes(IVecInt assumptions) {
        return computeAllMUSes(assumptions, SolutionFoundListener.VOID);
    }

    /**
     * Computes all the MUSes associated to the set of constraints added to the
     * solver
     * 
     * @param assumptions
     *            the assumptions under which the MUSes must be computed.
     * @param listener
     *            a listener to call when an MUS is found
     * @return a list containing all the MUSes
     */
    public List<IVecInt> computeAllMUSes(IVecInt assumptions,
            SolutionFoundListener listener) {
        if (secondPhaseClauses.isEmpty()) {
            computeAllMSS(assumptions);
        }
        ISolver solver = factory.defaultSolver();
        for (IVecInt v : secondPhaseClauses) {
            try {
                solver.addClause(v);
            } catch (ContradictionException e) {
                return musList;
            }
        }
        AbstractMinimalModel minSolver = new Minimal4InclusionModel(solver,
                Minimal4InclusionModel.positiveLiterals(solver));
        return computeAllMUSes(assumptions, listener, minSolver);
    }

    public List<IVecInt> computeAllMUSesOrdered(
            SolutionFoundListener listener) {
        return computeAllMUSesOrdered(VecInt.EMPTY, listener);
    }

    public List<IVecInt> computeAllMUSesOrdered(IVecInt assumptions,
            SolutionFoundListener listener) {
        if (secondPhaseClauses.isEmpty()) {
            computeAllMSS();
        }
        ISolver solver = factory.defaultSolver();
        for (IVecInt v : secondPhaseClauses) {
            try {
                solver.addClause(v);
            } catch (ContradictionException e) {
                return musList;
            }
        }
        AbstractMinimalModel minSolver = new Minimal4CardinalityModel(solver,
                Minimal4InclusionModel.positiveLiterals(solver));
        return computeAllMUSes(assumptions, listener, minSolver);
    }

    private List<IVecInt> computeAllMUSes(IVecInt assumptions,
            SolutionFoundListener listener, ISolver minSolver) {
        if (css.isVerbose()) {
            System.out.println(css.getLogPrefix() + "Computing all MUSes ...");
        }
        css.internalState();

        IVecInt mus;

        IVecInt blockingClause;

        try {

            while (minSolver.isSatisfiable(assumptions)) {
                blockingClause = new VecInt();
                mus = new VecInt();

                int[] model = minSolver.model();

                for (int i = 0; i < model.length; i++) {
                    if (model[i] > 0) {
                        blockingClause.push(-model[i]);
                        mus.push(model[i]);
                    }
                }
                musList.add(mus);
                listener.onSolutionFound(mus);
                try {
                    minSolver.addBlockingClause(blockingClause);
                } catch (ContradictionException e) {
                    break;
                }
            }
        } catch (TimeoutException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Timeout when computing all muses", e);
        }
        if (css.isVerbose()) {
            System.out.println(css.getLogPrefix() + "... done.");
        }
        css.externalState();
        return musList;
    }

    public List<IVecInt> computeAllMSS() {
        return computeAllMSS(VecInt.EMPTY);
    }

    public List<IVecInt> computeAllMSS(IVecInt assumptions) {
        return computeAllMSS(assumptions, SolutionFoundListener.VOID);
    }

    public List<IVecInt> computeAllMSS(SolutionFoundListener mssListener) {
        return computeAllMSS(VecInt.EMPTY, mssListener);
    }

    public List<IVecInt> computeAllMSS(IVecInt assumptions,
            SolutionFoundListener listener) {
        IVecInt pLits = new VecInt();
        for (Integer i : css.getAddedVars()) {
            pLits.push(i);
        }

        AbstractMinimalModel min4Inc = new Minimal4InclusionModel(css, pLits);
        return computeAllMSS(assumptions, listener, min4Inc, pLits);
    }

    public List<IVecInt> computeAllMSSOrdered(IVecInt assumptions,
            SolutionFoundListener listener) {
        IVecInt pLits = new VecInt();
        for (Integer i : css.getAddedVars()) {
            pLits.push(i);
        }

        AbstractMinimalModel min4Inc = new Minimal4CardinalityModel(css, pLits);
        return computeAllMSS(assumptions, listener, min4Inc, pLits);
    }

    private List<IVecInt> computeAllMSS(IVecInt assumptions,
            SolutionFoundListener listener, ISolver min4Inc, IVecInt pLits) {
        if (css.isVerbose()) {
            System.out.println(css.getLogPrefix() + "Computing all MSSes ...");
        }
        css.internalState();
        int nVar = css.nVars();

        IVecInt blockingClause;

        IVecInt secondPhaseClause;

        IVecInt fullMSS = new VecInt();
        IVecInt mss;

        int clause;

        for (int i = 0; i < css.getAddedVars().size(); i++) {
            fullMSS.push(i + 1);
        }

        // first phase
        try {

            while (min4Inc.isSatisfiable(assumptions)) {
                int[] fullmodel = min4Inc.modelWithInternalVariables();

                mss = new VecInt();
                fullMSS.copyTo(mss);

                blockingClause = new VecInt();
                secondPhaseClause = new VecInt();
                for (int i = 0; i < pLits.size(); i++) {
                    clause = Math.abs(pLits.get(i));
                    if (fullmodel[clause - 1] > 0) {
                        blockingClause.push(-clause);
                        secondPhaseClause.push(clause - nVar);
                        mss.remove(clause - nVar);
                    }
                }

                mssList.add(mss);

                listener.onSolutionFound(mss);

                secondPhaseClauses.add(secondPhaseClause);
                try {
                    css.addBlockingClause(blockingClause);
                } catch (ContradictionException e) {
                    Logger.getLogger("org.sat4j.core").log(Level.INFO,
                            "Trivial inconsistency", e);
                    break;
                }
            }

        } catch (TimeoutException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Timeout during the first stage", e);
        }
        if (css.isVerbose()) {
            System.out.println(css.getLogPrefix() + "... done.");
        }
        css.externalState();
        return mssList;
    }

    public List<IVecInt> getMssList() {
        return mssList;
    }

}
