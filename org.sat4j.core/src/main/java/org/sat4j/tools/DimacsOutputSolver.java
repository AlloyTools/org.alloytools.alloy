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

import java.io.ObjectInputStream;
import java.io.PrintWriter;
import java.util.Collection;

import org.sat4j.annotations.Feature;
import org.sat4j.specs.AssignmentOrigin;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IGroupSolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.UnitClauseConsumer;

/**
 * Solver used to display in a writer the CNF instance in Dimacs format.
 * 
 * That solver is useful to produce CNF files to be used by third party solvers.
 * 
 * @author leberre
 * 
 */
@Feature("solver")
public class DimacsOutputSolver extends AbstractOutputSolver
        implements IGroupSolver {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private transient PrintWriter out;

    public DimacsOutputSolver() {
        this(new PrintWriter(System.out, true));
    }

    public DimacsOutputSolver(PrintWriter pw) {
        this.out = pw;
    }

    private void readObject(ObjectInputStream stream) {
        this.out = new PrintWriter(System.out, true);
    }

    public int newVar() {
        return 0;
    }

    @Override
    public int newVar(int howmany) {
        this.out.print("p cnf " + howmany);
        this.nbvars = howmany;
        return 0;
    }

    public void setExpectedNumberOfClauses(int nb) {
        this.out.println(" " + nb);
        this.nbclauses = nb;
        this.fixedNbClauses = true;
    }

    public IConstr addClause(IVecInt literals) throws ContradictionException {
        if (this.firstConstr) {
            if (!this.fixedNbClauses) {
                this.out.println(" XXXXXX");
            }
            this.firstConstr = false;
        }
        for (IteratorInt iterator = literals.iterator(); iterator.hasNext();) {
            this.out.print(iterator.next() + " ");
        }
        this.out.println("0");
        return null;
    }

    public IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException {
        if (degree > 1) {
            throw new UnsupportedOperationException(
                    "Not a clausal problem! degree " + degree);
        }
        assert degree == 1;
        if (this.firstConstr) {
            if (!this.fixedNbClauses) {
                this.out.println("XXXXXX");
            }
            this.firstConstr = false;
        }
        for (int i = 0; i <= literals.size(); i++) {
            for (int j = i + 1; j < literals.size(); j++) {
                this.out.println(
                        "" + -literals.get(i) + " " + -literals.get(j) + " 0");
            }
        }
        return null;
    }

    public IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException {
        if (degree > 1) {
            throw new UnsupportedOperationException(
                    "Not a clausal problem! degree " + degree);
        }
        assert degree == 1;
        return addClause(literals);
    }

    public IConstr addExactly(IVecInt literals, int n)
            throws ContradictionException {
        if (n > 1) {
            throw new UnsupportedOperationException(
                    "Not a clausal problem! degree " + n);
        }
        assert n == 1;
        addAtMost(literals, n);
        addAtLeast(literals, n);
        return null;
    }

    public void reset() {
        this.fixedNbClauses = false;
        this.firstConstr = true;

    }

    public String toString(String prefix) {
        return "Dimacs output solver";
    }

    @Override
    public int nConstraints() {
        return this.nbclauses;
    }

    @Override
    public int nVars() {
        return this.nbvars;
    }

    /**
     * @since 2.1
     */
    public int nextFreeVarId(boolean reserve) {
        if (reserve) {
            return ++this.nbvars;
        }
        return this.nbvars + 1;
    }

    /**
     * @since 2.3.1
     */
    public int[] modelWithInternalVariables() {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.3.1
     */
    public int realNumberOfVariables() {
        return this.nbvars;
    }

    /**
     * @since 2.3.1
     */
    public void registerLiteral(int p) {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.3.2
     */
    public boolean primeImplicant(int p) {
        throw new UnsupportedOperationException();
    }

    /**
     * @since 2.3.3
     */
    public void printStat(PrintWriter out) {
        // do nothing
    }

    /**
     * @since 2.3.3
     */
    public void printInfos(PrintWriter out) {
        // do nothing
    }

    public IConstr addClause(IVecInt literals, int desc)
            throws ContradictionException {
        this.out.print(desc + "> ");
        for (IteratorInt iterator = literals.iterator(); iterator.hasNext();) {
            this.out.print(iterator.next() + " ");
        }
        this.out.println("0");
        return null;
    }

    public Collection<Integer> getAddedVars() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public IConstr addParity(IVecInt literals, boolean even) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    public AssignmentOrigin getOriginInModel(int p) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public void setUnitClauseConsumer(UnitClauseConsumer ucc) {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

    @Override
    public int[] decisions() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }
}
