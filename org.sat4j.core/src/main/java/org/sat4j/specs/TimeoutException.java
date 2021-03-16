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
 * Exception launched when the solver cannot solve a problem within its allowed
 * time. Note that the name of that exception is subject to change since a
 * TimeoutException must also be launched by incomplete solvers to reply
 * "Unknown".
 * 
 * @author leberre
 */
public class TimeoutException extends Exception {

    private static final long serialVersionUID = 1L;

    /**
     * Constructor for TimeoutException.
     */
    public TimeoutException() {
        super();
    }

    /**
     * Constructor for TimeoutException.
     * 
     * @param message
     *            the error message
     */
    public TimeoutException(String message) {
        super(message);
    }

    /**
     * Constructor for TimeoutException.
     * 
     * @param message
     *            the error message
     * @param cause
     *            the cause of the exception
     */
    public TimeoutException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructor for TimeoutException.
     * 
     * @param cause
     *            the cause of the exception
     */
    public TimeoutException(Throwable cause) {
        super(cause);
    }

}
