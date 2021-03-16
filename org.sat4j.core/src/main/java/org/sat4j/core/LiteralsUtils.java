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
package org.sat4j.core;

/**
 * Utility methods to avoid using bit manipulation inside code. One should use
 * Java 1.5 import static feature to use it without class qualification inside
 * the code.
 * 
 * In the DIMACS format, the literals are represented by signed integers, 0
 * denoting the end of the clause. In the solver, the literals are represented
 * by positive integers, in order to use them as index in arrays for instance.
 * 
 * <pre>
 *  int p : a literal (p&gt;1)
 *  p &circ; 1 : the negation of the literal
 *  p &gt;&gt; 1 : the DIMACS number representing the variable.
 *  int v : a DIMACS variable (v&gt;0)
 *  v &lt;&lt; 1 : a positive literal for that variable in the solver.
 *  v &lt;&lt; 1 &circ; 1 : a negative literal for that variable.
 * </pre>
 * 
 * @author leberre
 * 
 */
public final class LiteralsUtils {

    private LiteralsUtils() {
        // no instance supposed to be created.
    }

    /**
     * Returns the variable associated to the literal
     * 
     * @param p
     *            a literal in internal representation
     * @return the Dimacs variable associated to that literal.
     */
    public static int var(int p) {
        assert p > 1;
        return p >> 1;
    }

    /**
     * Returns the opposite literal.
     * 
     * @param p
     *            a literal in internal representation
     * @return the opposite literal in internal representation
     */
    public static int neg(int p) {
        return p ^ 1;
    }

    /**
     * Returns the positive literal associated with a variable.
     * 
     * @param var
     *            a variable in Dimacs format
     * @return the positive literal associated with this variable in internal
     *         representation
     */
    public static int posLit(int var) {
        return var << 1;
    }

    /**
     * Returns the negative literal associated with a variable.
     * 
     * @param var
     *            a variable in Dimacs format
     * @return the negative literal associated with this variable in internal
     *         representation
     */
    public static int negLit(int var) {
        return var << 1 ^ 1;
    }

    /**
     * decode the internal representation of a literal in internal
     * representation into Dimacs format.
     * 
     * @param p
     *            the literal in internal representation
     * @return the literal in dimacs representation
     */
    public static int toDimacs(int p) {
        return ((p & 1) == 0 ? 1 : -1) * (p >> 1);
    }

    /**
     * encode the classical Dimacs representation (negated integers for negated
     * literals) into the internal format.
     * 
     * @param x
     *            the literal in Dimacs format
     * @return the literal in internal format
     * @since 2.2
     */
    public static int toInternal(int x) {
        return x < 0 ? -x << 1 ^ 1 : x << 1;
    }

    /**
     * decode the internal representation in an OPB-like representation.
     * 
     * Note that we use the literal representation (~xi) which may not be
     * supoorted by all OPB solvers.
     * 
     * @param p
     *            a literal in internal format
     * @return that literal using the OPB literal format.
     */
    public static String toOPB(int p) {
        return ((p & 1) == 0 ? "" : "~") + "x" + (p >> 1);
    }
}
