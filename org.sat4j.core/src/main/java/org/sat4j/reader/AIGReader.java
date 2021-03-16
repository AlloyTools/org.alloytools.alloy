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

import org.sat4j.annotations.Feature;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.tools.GateTranslator;

/**
 * Reader for the Binary And Inverter Graph format defined by Armin Biere.
 * 
 * @author daniel
 * 
 */
@Feature(value = "reader", parent = "expert")
public class AIGReader extends Reader {

    private static final int FALSE = 0;

    private static final int TRUE = 1;

    private final GateTranslator solver;

    private int maxvarid;

    private int nbinputs;

    AIGReader(ISolver s) {
        this.solver = new GateTranslator(s);
    }

    @Override
    public String decode(int[] model) {
        StringBuilder stb = new StringBuilder();
        for (int i = 0; i < this.nbinputs; i++) {
            stb.append(model[i] > 0 ? 1 : 0);
        }
        return stb.toString();
    }

    @Override
    public void decode(int[] model, PrintWriter out) {
        for (int i = 0; i < this.nbinputs; i++) {
            out.print(model[i] > 0 ? 1 : 0);
        }
    }

    int parseInt(InputStream in, char expected)
            throws IOException, ParseFormatException {
        int res, ch;
        ch = in.read();

        if (ch < '0' || ch > '9') {
            throw new ParseFormatException("expected digit");
        }
        res = ch - '0';

        while ((ch = in.read()) >= '0' && ch <= '9') {
            res = 10 * res + ch - '0';
        }

        if (ch != expected) {
            throw new ParseFormatException("unexpected character");
        }

        return res;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.reader.Reader#parseInstance(java.io.InputStream)
     */
    @Override
    public IProblem parseInstance(InputStream in)
            throws ParseFormatException, ContradictionException, IOException {
        if (in.read() != 'a' || in.read() != 'i' || in.read() != 'g'
                || in.read() != ' ') {
            throw new ParseFormatException("AIG format only!");
        }
        this.maxvarid = parseInt(in, ' ');
        this.nbinputs = parseInt(in, ' ');
        int nblatches = parseInt(in, ' ');
        if (nblatches > 0) {
            throw new ParseFormatException(
                    "CNF conversion cannot handle latches!");
        }
        int nboutputs = parseInt(in, ' ');
        if (nboutputs > 1) {
            throw new ParseFormatException(
                    "CNF conversion allowed for single output circuit only!");
        }
        int nbands = parseInt(in, '\n');
        this.solver.newVar(this.maxvarid + 1);
        this.solver.setExpectedNumberOfClauses(3 * nbands + 2);
        if (nboutputs > 0) {
            assert nboutputs == 1;
            int output0 = parseInt(in, '\n');
            readAnd(nbands, output0, in, 2 * (this.nbinputs + 1));
        }
        return this.solver;
    }

    static int safeGet(InputStream in)
            throws IOException, ParseFormatException {
        int ch = in.read();
        if (ch == -1) {
            throw new ParseFormatException("AIG Error, EOF met too early");
        }
        return ch;
    }

    static int decode(InputStream in) throws IOException, ParseFormatException {
        int x = 0, i = 0;
        int ch;

        while (((ch = safeGet(in)) & 0x80) > 0) {
            System.out.println("=>" + ch);
            x |= (ch & 0x7f) << 7 * i++;
        }
        return x | ch << 7 * i;
    }

    private void readAnd(int nbands, int output0, InputStream in, int startid)
            throws ContradictionException, IOException, ParseFormatException {
        int lhs = startid;
        for (int i = 0; i < nbands; i++) {
            int delta0 = decode(in);
            int delta1 = decode(in);
            int rhs0 = lhs - delta0;
            int rhs1 = rhs0 - delta1;
            this.solver.and(toDimacs(lhs), toDimacs(rhs0), toDimacs(rhs1));
            lhs += 2;
        }
        this.solver.gateTrue(this.maxvarid + 1);
        this.solver.gateTrue(toDimacs(output0));
    }

    private int toDimacs(int v) {
        if (v == FALSE) {
            return -(this.maxvarid + 1);
        }
        if (v == TRUE) {
            return this.maxvarid + 1;
        }
        int var = v >> 1;
        if ((v & 1) == 0) {
            return var;
        }
        return -var;
    }
}
