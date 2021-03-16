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
package org.sat4j.reader;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.Serializable;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * Very simple Dimacs file parser. Allow solvers to read the constraints from a
 * Dimacs formatted file. It should be used that way:
 * 
 * <pre>
 * DimacsReader solver = new DimacsReader(SolverFactory.OneSolver());
 * solver.readInstance(&quot;mybench.cnf&quot;);
 * if (solver.isSatisfiable()) {
 *     // SAT case
 * } else {
 *     // UNSAT case
 * }
 * </pre>
 * 
 * That parser is not used for efficiency reasons. It will be updated with Java
 * 1.5 scanner feature.
 * 
 * @version 1.0
 * @author dlb
 * @author or
 */
@Feature(value = "reader", parent = "expert")
public class DimacsReader extends Reader implements Serializable {

    private static final long serialVersionUID = 1L;

    protected int expectedNbOfConstr; // as announced on the p cnf line

    protected final ISolver solver;

    private boolean checkConstrNb = true;

    protected final String formatString;

    /**
     * @since 2.1
     */
    protected EfficientScanner scanner;

    public DimacsReader(ISolver solver) {
        this(solver, "cnf");
    }

    public DimacsReader(ISolver solver, String format) {
        this.solver = solver;
        this.formatString = format;
    }

    public void disableNumberOfConstraintCheck() {
        this.checkConstrNb = false;
    }

    /**
     * Skip comments at the beginning of the input stream.
     * 
     * @throws IOException
     *             if an IO problem occurs.
     * @since 2.1
     */
    protected void skipComments() throws IOException {
        this.scanner.skipComments();
    }

    /**
     * @throws IOException
     *             iff an IO occurs
     * @throws ParseFormatException
     *             if the input stream does not comply with the DIMACS format.
     * @since 2.1
     */
    protected void readProblemLine() throws IOException, ParseFormatException {

        String line = this.scanner.nextLine().trim();

        if (line == null) {
            throw new ParseFormatException(
                    "premature end of file: <p cnf ...> expected");
        }
        String[] tokens = line.split("\\s+");
        if (tokens.length < 4 || !"p".equals(tokens[0])
                || !this.formatString.equals(tokens[1])) {
            throw new ParseFormatException("problem line expected (p cnf ...)");
        }

        int vars;

        // reads the max var id
        vars = Integer.parseInt(tokens[2]);
        assert vars > 0;
        this.solver.newVar(vars);
        // reads the number of clauses
        this.expectedNbOfConstr = Integer.parseInt(tokens[3]);
        assert this.expectedNbOfConstr > 0;
        this.solver.setExpectedNumberOfClauses(this.expectedNbOfConstr);
    }

    /**
     * @since 2.1
     */
    protected IVecInt literals = new VecInt();

    /**
     * @throws IOException
     *             iff an IO problems occurs
     * @throws ParseFormatException
     *             if the input stream does not comply with the DIMACS format.
     * @throws ContradictionException
     *             si le probl?me est trivialement inconsistant.
     * @since 2.1
     */
    protected void readConstrs()
            throws IOException, ParseFormatException, ContradictionException {
        int realNbOfConstr = 0;

        this.literals.clear();
        boolean needToContinue = true;

        while (needToContinue) {
            boolean added = false;
            if (this.scanner.eof()) {
                // end of file
                if (this.literals.size() > 0) {
                    // no 0 end the last clause
                    flushConstraint();
                    added = true;
                }
                needToContinue = false;
            } else {
                if (this.scanner.currentChar() == 'c') {
                    // ignore comment line
                    this.scanner.skipRestOfLine();
                    continue;
                }
                if (this.scanner.currentChar() == '%'
                        && this.expectedNbOfConstr == realNbOfConstr) {
                    if (this.solver.isVerbose()) {
                        System.out.println(
                                "Ignoring the rest of the file (SATLIB format");
                    }
                    break;
                }
                added = handleLine();
            }
            if (added) {
                realNbOfConstr++;
            }
        }
        if (this.checkConstrNb && this.expectedNbOfConstr != realNbOfConstr) {
            throw new ParseFormatException(
                    "wrong nbclauses parameter. Found " + realNbOfConstr + ", "
                            + this.expectedNbOfConstr + " expected");
        }
    }

    /**
     * 
     * @throws ContradictionException
     * @since 2.1
     */
    protected void flushConstraint() throws ContradictionException {
        try {
            this.solver.addClause(this.literals);
        } catch (IllegalArgumentException ex) {
            if (isVerbose()) {
                System.err.println("c Skipping constraint " + this.literals);
            }
        }
    }

    /**
     * @since 2.1
     */
    protected boolean handleLine()
            throws ContradictionException, IOException, ParseFormatException {
        int lit;
        boolean added = false;
        while (!this.scanner.eof()) {
            lit = this.scanner.nextInt();
            if (lit == 0) {
                if (this.literals.size() > 0) {
                    flushConstraint();
                    this.literals.clear();
                    added = true;
                }
                break;
            }
            this.literals.push(lit);
        }
        return added;
    }

    @Override
    public IProblem parseInstance(InputStream in)
            throws ParseFormatException, ContradictionException, IOException {
        this.scanner = new EfficientScanner(in);
        return parseInstance();
    }

    /**
     * @param in
     *            the input stream
     * @throws ParseFormatException
     *             if the input stream does not comply with the DIMACS format.
     * @throws ContradictionException
     *             si le probl?me est trivialement inconsitant
     */
    private IProblem parseInstance()
            throws ParseFormatException, ContradictionException {
        this.solver.reset();
        try {
            skipComments();
            readProblemLine();
            readConstrs();
            this.scanner.close();
            return this.solver;
        } catch (IOException e) {
            throw new ParseFormatException(e);
        } catch (NumberFormatException e) {
            throw new ParseFormatException("integer value expected ");
        }
    }

    @Override
    public String decode(int[] model) {
        StringBuilder stb = new StringBuilder();
        for (int element : model) {
            stb.append(element);
            stb.append(" ");
        }
        stb.append("0");
        return stb.toString();
    }

    @Override
    public void decode(int[] model, PrintWriter out) {
        for (int element : model) {
            out.print(element);
            out.print(" ");
        }
        out.print("0");
    }

    protected ISolver getSolver() {
        return this.solver;
    }
}
