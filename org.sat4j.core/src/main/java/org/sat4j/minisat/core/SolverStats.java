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
package org.sat4j.minisat.core;

import java.io.PrintWriter;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

/**
 * Contains some statistics regarding the search.
 * 
 * @author daniel
 * 
 */
public class SolverStats implements Serializable {
    private static final long serialVersionUID = 1L;

    private int starts;

    private long decisions;

    private long propagations;

    private long inspects;

    private long conflicts;

    private long learnedliterals;

    private long learnedbinaryclauses;

    private long learnedternaryclauses;

    private long learnedclauses;

    private long ignoredclauses;

    private long rootSimplifications;

    private long reducedliterals;

    private long changedreason;

    private int reduceddb;

    private int shortcuts;

    private long updateLBD;

    private int importedUnits;

    public void reset() {
        this.starts = 0;
        this.decisions = 0;
        this.propagations = 0;
        this.inspects = 0;
        this.shortcuts = 0;
        this.conflicts = 0;
        this.learnedliterals = 0;
        this.learnedclauses = 0;
        this.ignoredclauses = 0;
        this.learnedbinaryclauses = 0;
        this.learnedternaryclauses = 0;
        this.rootSimplifications = 0;
        this.reducedliterals = 0;
        this.changedreason = 0;
        this.reduceddb = 0;
        this.updateLBD = 0;
        this.importedUnits = 0;
    }

    public void printStat(PrintWriter out, String prefix) {
        out.println(prefix + "starts\t\t: " + this.getStarts());
        out.println(prefix + "conflicts\t\t: " + this.conflicts);
        out.println(prefix + "decisions\t\t: " + this.decisions);
        out.println(prefix + "propagations\t\t: " + this.propagations);
        out.println(prefix + "inspects\t\t: " + this.inspects);
        out.println(prefix + "shortcuts\t\t: " + this.shortcuts);
        out.println(prefix + "learnt literals\t: " + this.learnedliterals);
        out.println(prefix + "learnt binary clauses\t: "
                + this.learnedbinaryclauses);
        out.println(prefix + "learnt ternary clauses\t: "
                + this.learnedternaryclauses);
        out.println(prefix + "learnt constraints\t: " + this.learnedclauses);
        out.println(prefix + "ignored constraints\t: " + this.ignoredclauses);
        out.println(
                prefix + "root simplifications\t: " + this.rootSimplifications);
        out.println(prefix + "removed literals (reason simplification)\t: "
                + this.reducedliterals);
        out.println(prefix + "reason swapping (by a shorter reason)\t: "
                + this.changedreason);
        out.println(prefix + "Calls to reduceDB\t: " + this.reduceddb);
        out.println(prefix + "Number of update (reduction) of LBD\t: "
                + this.updateLBD);
        out.println(prefix + "Imported unit clauses\t: " + this.importedUnits);
    }

    public Map<String, Number> toMap() {
        Map<String, Number> map = new HashMap<String, Number>();
        Class<?> clazz = this.getClass();
        do {
            for (Field f : clazz.getDeclaredFields()) {
                try {
                    f.setAccessible(true);
                    Object value = f.get(this);
                    if (!"serialVersionUID".equals(f.getName())
                            && value instanceof Number) {
                        map.put(f.getName(), (Number) value);
                    }
                } catch (IllegalArgumentException e) {
                    // ignores silently
                } catch (IllegalAccessException e) {
                    // ignores silently
                }
            }
            clazz = clazz.getSuperclass();
        } while (clazz != null);
        return map;
    }

    public int getStarts() {
        return starts;
    }

    public void incStarts() {
        this.starts++;
    }

    public long getDecisions() {
        return decisions;
    }

    public void incDecisions() {
        this.decisions++;
    }

    public long getPropagations() {
        return propagations;
    }

    public void incPropagations() {
        this.propagations++;
    }

    public long getInspects() {
        return inspects;
    }

    public void incInspects() {
        this.inspects++;
    }

    public long getConflicts() {
        return conflicts;
    }

    public void incConflicts() {
        this.conflicts++;
    }

    public long getLearnedliterals() {
        return learnedliterals;
    }

    public void incLearnedliterals() {
        this.learnedliterals++;
    }

    public long getLearnedbinaryclauses() {
        return learnedbinaryclauses;
    }

    public void incLearnedbinaryclauses() {
        this.learnedbinaryclauses++;
    }

    public long getLearnedternaryclauses() {
        return learnedternaryclauses;
    }

    public void incLearnedternaryclauses() {
        this.learnedternaryclauses++;
    }

    public long getLearnedclauses() {
        return learnedclauses;
    }

    public void incLearnedclauses() {
        this.learnedclauses++;
    }

    public long getIgnoredclauses() {
        return ignoredclauses;
    }

    public void incIgnoredclauses() {
        this.ignoredclauses++;
    }

    public long getRootSimplifications() {
        return rootSimplifications;
    }

    public void incRootSimplifications() {
        this.rootSimplifications++;
    }

    public long getReducedliterals() {
        return reducedliterals;
    }

    public void incReducedliterals(int increment) {
        this.reducedliterals += increment;
    }

    public long getChangedreason() {
        return changedreason;
    }

    public void incChangedreason() {
        this.changedreason++;
    }

    public int getReduceddb() {
        return reduceddb;
    }

    public void incReduceddb() {
        this.reduceddb++;
    }

    public int getShortcuts() {
        return shortcuts;
    }

    public void incShortcuts() {
        this.shortcuts++;
    }

    public long getUpdateLBD() {
        return updateLBD;
    }

    public void incUpdateLBD() {
        this.updateLBD++;
    }

    public int getImportedUnits() {
        return importedUnits;
    }

    public void incImportedUnits(int increment) {
        this.importedUnits += increment;
    }
}
