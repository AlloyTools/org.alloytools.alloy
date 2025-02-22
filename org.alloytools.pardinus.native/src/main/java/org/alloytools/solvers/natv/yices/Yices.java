/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package org.alloytools.solvers.natv.yices;

import kodkod.engine.satlab.NativeSolver;

/**
 * Java wrapper for the Yices solver.
 *
 * @author Tiago Guimarães // [HASLab] target-oriented model finding
 */
final public class Yices extends NativeSolver {

    private boolean makearray;
    protected long  array = 0;

    /**
     * Constructs a new Yices wrapper.
     */
    public Yices() {
        super(NativeSolver.make("Yices", Yices::make));
        makearray = true;
        array = allocArray();
    }

    /**
     * Returns a pointer to an instance of Yices.
     *
     * @return a pointer to an instance of Yices.
     */
    private static native long make();

    private static native long allocArray();

    @Override
    public void free(long peer) {
        if (array != 0) {
            free(peer, array);
            //System.out.println("free");
            array = 0;
        }
    }

    protected native void free(long peer, long array);

    @Override
    public void addVariables(long peer, int numVariables) {
        //System.out.println(peer);
        natAddVariables(peer, array, numVariables, (super.numberOfVariables()) - numVariables);
    }

    native long natAddVariables(long peer, long array, int numVariables, int currentVarCount);

    @Override
    public boolean addClause(long peer, int[] lits) {
        boolean res = natAddClause(peer, lits, makearray, array);
        makearray = false;
        return res;
    }

    native boolean natAddClause(long peer, int[] lits, boolean makearray, long array);

    @Override
    public native boolean solve(long peer);

    @Override
    public native boolean valueOf(long peer, int literal);

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Yices";
    }

}
