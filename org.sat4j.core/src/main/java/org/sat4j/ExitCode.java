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

/**
 * Enumeration allowing to manage easily exit code for the SAT and PB
 * Competitions.
 * 
 * @author leberre
 * 
 */
public enum ExitCode {

    OPTIMUM_FOUND(30, "OPTIMUM FOUND"),
    UPPER_BOUND(30, "UPPER BOUND"),
    SATISFIABLE(10, "SATISFIABLE"),
    UNKNOWN(0, "UNKNOWN"),
    UNSATISFIABLE(20, "UNSATISFIABLE");

    /** value of the exit code. */
    private final int value;

    /** alternative textual representation of the exit code. */
    private final String str;

    /**
     * creates an exit code with a given value and an alternative textual
     * representation.
     * 
     * @param i
     *            the value of the exit code
     * @param str
     *            the alternative textual representation
     */
    private ExitCode(final int i, final String str) {
        this.value = i;
        this.str = str;
    }

    /**
     * @return the exit code value
     */
    public int value() {
        return this.value;
    }

    /**
     * @return the name of the enum or the alternative textual representation if
     *         any.
     */
    @Override
    public String toString() {
        return this.str;
    }
}
