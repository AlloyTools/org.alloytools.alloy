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

import java.io.Serializable;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * Very simple Dimacs array reader. Allow solvers to read the constraints from
 * arrays that effectively contain Dimacs formatted lines (without the
 * terminating 0).
 * 
 * Adaptation of org.sat4j.reader.DimacsReader.
 * 
 * @author dlb
 * @author fuhs
 */
public class DimacsArrayReader implements Serializable {

    private static final long serialVersionUID = 1L;

    protected final ISolver solver;

    public DimacsArrayReader(ISolver solver) {
        this.solver = solver;
    }

    protected boolean handleConstr(int gateType, int output, int[] inputs)
            throws ContradictionException {
        IVecInt literals = new VecInt(inputs);
        this.solver.addClause(literals);
        return true;
    }

    /**
     * @param gateType
     *            gateType[i] is the type of gate i according to the Extended
     *            Dimacs specs; ignored in DimacsArrayReader, but important for
     *            inheriting classes
     * @param outputs
     *            outputs[i] is the number of the output; ignored in
     *            DimacsArrayReader
     * @param inputs
     *            inputs[i] contains the clauses in DimacsArrayReader; an
     *            overriding class might have it contain the inputs of the
     *            current gate
     * @param maxVar
     *            the maximum number of assigned ids
     * @throws ContradictionException
     *             si le probleme est trivialement inconsitant
     */
    public ISolver parseInstance(int[] gateType, int[] outputs, int[][] inputs,
            int maxVar) throws ContradictionException {
        this.solver.reset();
        this.solver.newVar(maxVar);
        this.solver.setExpectedNumberOfClauses(outputs.length);
        for (int i = 0; i < outputs.length; ++i) {
            handleConstr(gateType[i], outputs[i], inputs[i]);
        }
        return this.solver;
    }

    public String decode(int[] model) {
        StringBuilder stb = new StringBuilder(4 * model.length);
        for (int element : model) {
            stb.append(element);
            stb.append(" ");
        }
        stb.append("0");
        return stb.toString();
    }

    protected ISolver getSolver() {
        return this.solver;
    }
}
