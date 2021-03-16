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

import java.io.Serializable;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.sat4j.specs.ISolver;

/**
 * A solver factory is responsible for providing prebuilt solvers to the end
 * user.
 * 
 * @author bourgeois
 */
public abstract class ASolverFactory<T extends ISolver>
        implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * This methods returns names of solvers to be used with the method
     * getSolverByName().
     * 
     * @return an array containing the names of all the solvers available in the
     *         library.
     * @see #createSolverByName(String)
     */
    public String[] solverNames() {
        List<String> l = new ArrayList<String>();
        Method[] solvers = this.getClass().getDeclaredMethods();
        for (Method solver : solvers) {
            if (solver.getParameterTypes().length == 0
                    && solver.getName().startsWith("new")) { //$NON-NLS-1$
                l.add(solver.getName().substring(3));
            }
        }
        Collections.sort(l);
        String[] names = new String[l.size()];
        l.toArray(names);
        return names;
    }

    /**
     * create a solver from its String name. the solvername Xxxx must map one of
     * the newXxxx methods.
     * 
     * @param solvername
     *            the name of the solver
     * @return an ISolver built using newSolvername. <code>null</code> if the
     *         solvername doesn't map one of the method of the factory.
     */
    @SuppressWarnings("unchecked")
    public T createSolverByName(String solvername) {
        try {
            Class<?>[] paramtypes = {};
            Method m = this.getClass().getMethod("new" + solvername, //$NON-NLS-1$
                    paramtypes);
            return (T) m.invoke(null, (Object[]) null);
        } catch (SecurityException e) {
            System.err.println(e.getLocalizedMessage());
        } catch (IllegalArgumentException e) {
            System.err.println(e.getLocalizedMessage());
        } catch (NoSuchMethodException e) {
            System.err.println(e.getLocalizedMessage());
        } catch (IllegalAccessException e) {
            System.err.println(e.getLocalizedMessage());
        } catch (InvocationTargetException e) {
            System.err.println(e.getLocalizedMessage());
        }
        return null;
    }

    /**
     * To obtain the default solver of the library. The solver is suitable to
     * solve huge SAT benchmarks. It should reflect state-of-the-art SAT
     * technologies.
     * 
     * For solving small/easy SAT benchmarks, use lightSolver() instead.
     * 
     * @return a solver from the factory
     * @see #lightSolver()
     */
    public abstract T defaultSolver();

    /**
     * To obtain a solver that is suitable for solving many small instances of
     * SAT problems.
     * 
     * The solver is not using sophisticated but costly reasoning and avoids to
     * allocate too much memory.
     * 
     * For solving bigger SAT benchmarks, use defaultSolver() instead.
     * 
     * @return a solver from the factory
     * @see #defaultSolver()
     */
    public abstract T lightSolver();
}
