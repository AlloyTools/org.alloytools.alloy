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

import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.sat4j.annotations.Feature;
import org.sat4j.core.Vec;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.Lbool;
import org.sat4j.specs.RandomAccessModel;
import org.sat4j.specs.SearchListenerAdapter;
import org.sat4j.specs.VarMapper;

/**
 * Class allowing to express the search as a tree in the dot language. The
 * resulting file can be viewed in a tool like
 * <a href="http://www.graphviz.org/">Graphviz</a>
 * 
 * To use only on small benchmarks.
 * 
 * Note that also does not make sense to use such a listener on a distributed or
 * remote solver.
 * 
 * @author daniel
 * @since 2.2
 */
@Feature("searchlistener")
public class DotSearchTracing<T> extends SearchListenerAdapter<ISolverService>
        implements VarMapper {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final Vec<String> stack;

    private String currentNodeName = null;

    private transient Writer out;

    private boolean assertive = false;

    private Map<Integer, T> mapping;

    /**
     * @since 2.1
     */
    public DotSearchTracing(final String fileNameToSave) {
        this.stack = new Vec<String>();
        try {
            this.out = new FileWriter(fileNameToSave);
        } catch (IOException e) {
            System.err.println("Problem when created file.");
        }
    }

    public void setMapping(Map<Integer, T> mapping) {
        this.mapping = mapping;
    }

    public String map(int dimacs) {
        if (this.mapping != null) {
            int var = Math.abs(dimacs);
            T t = this.mapping.get(var);
            if (t != null) {
                if (dimacs > 0) {
                    return t.toString();
                }
                return "-" + t.toString();
            }
        }
        return Integer.toString(dimacs);
    }

    @Override
    public final void assuming(final int p) {
        final int absP = Math.abs(p);
        String newName;

        if (this.currentNodeName == null) {
            newName = Integer.toString(absP);
            this.stack.push(newName);
            saveLine(lineTab("\"" + newName + "\"" + "[label=\"" + map(p)
                    + "\", shape=circle, color=blue, fontcolor=white, style=filled]"));
        } else {
            newName = this.currentNodeName;
            this.stack.push(newName);
            saveLine(lineTab("\"" + newName + "\"" + "[label=\"" + map(p)
                    + "\", shape=circle, color=blue, fontcolor=white, style=filled]"));
        }
        this.currentNodeName = newName;
    }

    /**
     * @since 2.1
     */
    @Override
    public final void propagating(final int p) {
        String newName = this.currentNodeName + "." + p + "." + this.assertive;

        if (this.currentNodeName == null) {
            saveLine(lineTab("\"null\" [label=\"\", shape=point]"));
        }
        final String couleur = this.assertive ? "orange" : "green";

        saveLine(lineTab("\"" + newName + "\"" + "[label=\"" + map(p)
                + "\",shape=point, color=black]"));
        saveLine(lineTab("\"" + this.currentNodeName + "\"" + " -- " + "\""
                + newName + "\"" + "[label=" + "\" " + map(p)
                + "\", fontcolor =" + couleur + ", color = " + couleur
                + ", style = bold]"));
        this.currentNodeName = newName;
        this.assertive = false;
    }

    @Override
    public final void enqueueing(final int p, IConstr reason) {
        if (reason != null) {
            String newName = this.currentNodeName + "." + p + ".propagated."
                    + this.assertive;
            saveLine(lineTab("\"" + newName + "\"" + "[label=\"" + map(p)
                    + "\",shape=point, color=black]"));
            saveLine(lineTab("\"" + this.currentNodeName + "\"" + " -- " + "\""
                    + newName + "\"" + "[label=" + "\" " + map(p)
                    + "\", fontcolor = gray, color = gray, style = bold]"));
            String reasonName = newName + ".reason";
            saveLine(lineTab(
                    "\"" + reasonName + "\" [label=\"" + reason.toString(this)
                            + "\", shape=box, color=\"gray\", style=dotted]"));
            saveLine("\"" + reasonName + "\"" + "--" + "\""
                    + this.currentNodeName + "\""
                    + "[label=\"\", color=gray, style=dotted]");
            this.currentNodeName = newName;
        }
    }

    @Override
    public final void backtracking(final int p) {
        final String temp = this.stack.last();
        this.stack.pop();
        saveLine("\"" + temp + "\"" + "--" + "\"" + this.currentNodeName + "\""
                + "[label=\"\", color=red, style=dotted]");
        this.currentNodeName = temp;
    }

    @Override
    public final void adding(final int p) {
        this.assertive = true;
    }

    /**
     * @since 2.1
     */
    @Override
    public final void learn(final IConstr constr) {
        String learned = this.currentNodeName + "_learned";
        saveLine(lineTab("\"" + learned + "\" [label=\"" + constr.toString(this)
                + "\", shape=box, color=\"orange\", style=dotted]"));
        saveLine("\"" + learned + "\"" + "--" + "\"" + this.currentNodeName
                + "\"" + "[label=\"\", color=orange, style=dotted]");
    }

    @Override
    public final void delete(final IConstr c) {
    }

    /**
     * @since 2.1
     */
    @Override
    public final void conflictFound(IConstr confl, int dlevel, int trailLevel) {
        saveLine(lineTab("\"" + this.currentNodeName + "\" [label=\""
                + confl.toString(this)
                + "\", shape=box, color=\"red\", fontcolor=white, style=filled]"));
    }

    /**
     * @since 2.1
     */
    @Override
    public final void conflictFound(int p) {
        saveLine(lineTab("\"" + this.currentNodeName
                + "\" [label=\"\", shape=box, color=\"red\", style=filled]"));
    }

    @Override
    public final void solutionFound(int[] model, RandomAccessModel lazyModel) {
        saveLine(lineTab("\"" + this.currentNodeName
                + "\" [label=\"\", shape=box, color=\"green\", style=filled]"));
    }

    @Override
    public final void beginLoop() {
    }

    @Override
    public final void start() {
        saveLine("graph G {");
    }

    /**
     * @since 2.1
     */
    @Override
    public final void end(Lbool result) {
        saveLine("}");
    }

    private String lineTab(final String line) {
        return "\t" + line;
    }

    private void saveLine(final String line) {
        try {
            this.out.write(line + '\n');
            if ("}".equals(line)) {
                this.out.close();
            }
        } catch (IOException e) {
            Logger.getLogger("org.sat4j.core").log(Level.INFO,
                    "Something went wrong when saving dot file", e);
        }
    }

    private void readObject(ObjectInputStream stream)
            throws IOException, ClassNotFoundException {
        // if the solver is serialized, out is linked to stdout
        stream.defaultReadObject();
        this.out = new PrintWriter(System.out);
    }
}
