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
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.Lbool;
import org.sat4j.specs.SearchListenerAdapter;

/**
 * @since 2.2
 */
@Feature("searchlistener")
public class ConflictLevelTracing
        extends SearchListenerAdapter<ISolverService> {

    /**
     * 
     */
    private int counter;

    private static final long serialVersionUID = 1L;

    private int nVar;
    private int maxDLevel;

    private final IVisualizationTool visuTool;
    private final IVisualizationTool restartVisuTool;
    private final IVisualizationTool cleanTool;

    public ConflictLevelTracing(IVisualizationTool visuTool,
            IVisualizationTool restartVisuTool, IVisualizationTool cleanTool) {
        this.visuTool = visuTool;
        this.restartVisuTool = restartVisuTool;
        this.cleanTool = cleanTool;

        this.counter = 1;
        this.maxDLevel = 0;
    }

    @Override
    public void conflictFound(IConstr confl, int dlevel, int trailLevel) {
        if (dlevel > this.maxDLevel) {
            this.maxDLevel = dlevel;
        }
        this.visuTool.addPoint(this.counter, dlevel);
        this.restartVisuTool.addInvisiblePoint(this.counter, this.maxDLevel);
        this.cleanTool.addInvisiblePoint(this.counter, this.maxDLevel);
        this.counter++;
    }

    @Override
    public void restarting() {
        this.restartVisuTool.addPoint(this.counter, this.maxDLevel);
        this.cleanTool.addPoint(this.counter, 0);
        this.visuTool.addInvisiblePoint(this.counter, this.nVar);
    }

    @Override
    public void end(Lbool result) {
        this.visuTool.end();
        this.cleanTool.end();
        this.restartVisuTool.end();
    }

    @Override
    public void start() {
        this.visuTool.init();
        this.restartVisuTool.init();
        this.cleanTool.init();
        this.counter = 1;
        this.maxDLevel = 0;
    }

    @Override
    public void init(ISolverService solverService) {
        this.nVar = solverService.nVars();
    }

    @Override
    public void cleaning() {
        this.restartVisuTool.addPoint(this.counter, 0);
        this.cleanTool.addPoint(this.counter, this.maxDLevel);
        this.visuTool.addInvisiblePoint(this.counter, this.nVar);
    }
}
