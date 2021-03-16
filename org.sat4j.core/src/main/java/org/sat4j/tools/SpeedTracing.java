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
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.Lbool;
import org.sat4j.specs.SearchListenerAdapter;

@Feature("searchlistener")
public class SpeedTracing extends SearchListenerAdapter<ISolverService> {

    private static final long serialVersionUID = 1L;

    private final IVisualizationTool visuTool;
    private final IVisualizationTool cleanVisuTool;
    private final IVisualizationTool restartVisuTool;

    private long begin, end;
    private int counter;
    private long index;

    private double maxY;

    public SpeedTracing(IVisualizationTool visuTool,
            IVisualizationTool cleanVisuTool,
            IVisualizationTool restartVisuTool) {
        this.visuTool = visuTool;
        this.cleanVisuTool = cleanVisuTool;
        this.restartVisuTool = restartVisuTool;

        visuTool.init();
        cleanVisuTool.init();
        restartVisuTool.init();

        this.begin = System.currentTimeMillis();
        this.counter = 0;
        this.index = 0;
        this.maxY = 0;
    }

    @Override
    public void propagating(int p) {
        this.end = System.currentTimeMillis();
        double y;
        if (this.end - this.begin >= 2000) {
            long tmp = this.end - this.begin;
            this.index += tmp;
            y = (this.counter * 1000.0) / tmp;
            if (y > this.maxY) {
                this.maxY = y;
            }
            this.visuTool.addPoint(this.index / 1000.0, y);
            this.cleanVisuTool.addPoint(this.index / 1000.0, 0);
            this.restartVisuTool.addPoint(this.index / 1000.0, 0);
            this.begin = System.currentTimeMillis();
            this.counter = 0;
        }
        this.counter++;
    }

    @Override
    public void end(Lbool result) {
        this.visuTool.end();
        this.cleanVisuTool.end();
        this.restartVisuTool.end();
    }

    @Override
    public void cleaning() {
        this.end = System.currentTimeMillis();
        long indexClean = this.index + this.end - this.begin;
        this.visuTool.addPoint(indexClean / 1000.0,
                (this.counter * 1000.0) / (this.end - this.begin));
        this.cleanVisuTool.addPoint(indexClean / 1000.0, this.maxY);
        this.restartVisuTool.addInvisiblePoint(indexClean, 0);
    }

    @Override
    public void restarting() {
        this.end = System.currentTimeMillis();
        long indexRestart = this.index + this.end - this.begin;
        double y = (this.counter * 1000.0) / (this.end - this.begin);
        this.visuTool.addPoint(indexRestart / 1000.0, y);
        if (y > this.maxY) {
            this.maxY = y;
        }
        this.restartVisuTool.addPoint(indexRestart / 1000.0, this.maxY);
        this.cleanVisuTool.addInvisiblePoint(indexRestart, 0);
    }

    @Override
    public void start() {
        this.visuTool.init();
        this.cleanVisuTool.init();
        this.restartVisuTool.init();

        this.begin = System.currentTimeMillis();
        this.counter = 0;
        this.index = 0;
    }
}
