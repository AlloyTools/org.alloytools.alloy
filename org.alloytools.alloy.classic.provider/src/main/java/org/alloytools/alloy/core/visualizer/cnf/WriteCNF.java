/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package org.alloytools.alloy.core.visualizer.cnf;

import kodkod.engine.satlab.SATSolver;

/**
 * An implementation of SATSolver that dumps the CNF to a file and then throws
 * an exception (this code is adapted from ExternalSolver from Kodkod).
 */

final class WriteCNF implements SATSolver {

    final StringBuilder buffer  = new StringBuilder(100_000);
    int                 vars    = 0;
    int                 clauses = 0;


    public WriteCNF() {
        //             p cnf 0000000000 00000000000
        buffer.append("                               \n");
    }

    @Override
    public void free() {
    }

    @Override
    public void addVariables(int numVars) {
        if (numVars >= 0)
            vars += numVars;
    }

    @Override
    public boolean addClause(int[] lits) {
        if (lits.length > 0) {
            clauses++;
            for (int i = 0; i < lits.length; i++)
                buffer.append(lits[i]).append(' ');
            buffer.append("0\n");
            return true;
        }
        return false;
    }

    @Override
    public int numberOfVariables() {
        return vars;
    }

    @Override
    public int numberOfClauses() {
        return clauses;
    }

    @Override
    public boolean solve() {
        return false;
    }

    @Override
    public boolean valueOf(int variable) {
        return false;
    }

    public StringBuilder getBuffer() {
        String header = "p cnf " + vars + " " + clauses;
        buffer.replace(0, header.length(), header);
        return buffer;
    }
}
