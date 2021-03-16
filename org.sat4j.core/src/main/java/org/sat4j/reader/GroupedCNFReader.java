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

import org.sat4j.annotations.Feature;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IGroupSolver;

@Feature(value = "reader", parent = "expert")
public class GroupedCNFReader extends DimacsReader {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private int numberOfComponents;

    private final IGroupSolver groupSolver;

    private int currentComponentIndex;

    public GroupedCNFReader(IGroupSolver solver) {
        super(solver, "gcnf");
        this.groupSolver = solver;
    }

    /**
     * @throws IOException
     *             iff an IO occurs
     * @throws ParseFormatException
     *             if the input stream does not comply with the DIMACS format.
     * @since 2.1
     */
    @Override
    protected void readProblemLine() throws IOException, ParseFormatException {

        String line = this.scanner.nextLine();
        assert line != null;
        line = line.trim();
        String[] tokens = line.split("\\s+");
        if (tokens.length < 5 || !"p".equals(tokens[0])
                || !this.formatString.equals(tokens[1])) {
            throw new ParseFormatException(
                    "problem line expected (p " + this.formatString + " ...)");
        }

        int vars;

        // reads the max var id
        vars = Integer.parseInt(tokens[2]);
        assert vars > 0;
        this.solver.newVar(vars);
        // reads the number of clauses
        this.expectedNbOfConstr = Integer.parseInt(tokens[3]);
        assert this.expectedNbOfConstr > 0;
        this.numberOfComponents = Integer.parseInt(tokens[4]);
        this.solver.setExpectedNumberOfClauses(this.expectedNbOfConstr);
    }

    /**
     * @since 2.1
     */
    @Override
    protected boolean handleLine()
            throws ContradictionException, IOException, ParseFormatException {
        int lit;
        boolean added = false;
        String component = this.scanner.next();
        if (!component.startsWith("{") || !component.endsWith("}")) {
            throw new ParseFormatException(
                    "Component index required at the beginning of the clause");
        }
        this.currentComponentIndex = Integer
                .valueOf(component.substring(1, component.length() - 1));
        if (this.currentComponentIndex < 0
                || this.currentComponentIndex > this.numberOfComponents) {
            throw new ParseFormatException(
                    "wrong component index: " + this.currentComponentIndex);
        }
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

    /**
     * 
     * @throws ContradictionException
     * @since 2.1
     */
    @Override
    protected void flushConstraint() throws ContradictionException {
        try {
            if (this.currentComponentIndex == 0) {
                this.groupSolver.addClause(this.literals);
            } else {
                this.groupSolver.addClause(this.literals,
                        this.currentComponentIndex);
            }
        } catch (IllegalArgumentException ex) {
            if (isVerbose()) {
                System.err.println("c Skipping constraint " + this.literals);
            }
        }
    }
}
