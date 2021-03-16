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
 * That enumeration defines the possible truth value for a variable: satisfied,
 * falsified or unknown/undefined.
 * 
 * (that class moved from org.sat4j.minisat.core in earlier version of SAT4J).
 * 
 * @author leberre
 * @since 2.1
 */
public final class Lbool {

    public static final Lbool FALSE = new Lbool("F");
    public static final Lbool TRUE = new Lbool("T");
    public static final Lbool UNDEFINED = new Lbool("U");

    static {
        // usual boolean rules for negation
        FALSE.opposite = TRUE;
        TRUE.opposite = FALSE;
        UNDEFINED.opposite = UNDEFINED;
    }

    private Lbool(String symbol) {
        this.symbol = symbol;
    }

    /**
     * boolean negation.
     * 
     * @return Boolean negation. The negation of UNDEFINED is UNDEFINED.
     */
    public Lbool not() {
        return this.opposite;
    }

    /**
     * Textual representation for the truth value.
     * 
     * @return "T","F" or "U"
     */
    @Override
    public String toString() {
        return this.symbol;
    }

    /**
     * The symbol representing the truth value.
     */
    private final String symbol;

    /**
     * the opposite truth value.
     */
    private Lbool opposite;

}
