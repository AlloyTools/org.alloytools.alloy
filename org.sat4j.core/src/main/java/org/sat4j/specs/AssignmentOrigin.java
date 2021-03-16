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
package org.sat4j.specs;

/**
 * Origin of the assignment of a literal in a model or implicant.
 * 
 * @author leberre
 * @since 2.3.6
 */
public enum AssignmentOrigin {
    UNASSIGNED((char) 27 + "[0;37m"), DECIDED(
            (char) 27 + "[0;32m"), PROPAGATED_ORIGINAL(
                    (char) 27 + "[0;31m"), PROPAGATED_LEARNED(
                            (char) 27 + "[0;34m"), DECIDED_PROPAGATED((char) 27
                                    + "[0;35m"), DECIDED_PROPAGATED_LEARNED(
                                            (char) 27
                                                    + "[0;36m"), DECIDED_CYCLE(
                                                            (char) 27
                                                                    + "[0;42m");

    public static final String BLANK = (char) 27 + "[0m";
    private final String color;

    AssignmentOrigin(String color) {
        this.color = color;
    }

    public String getColor() {
        return color;
    }
}
