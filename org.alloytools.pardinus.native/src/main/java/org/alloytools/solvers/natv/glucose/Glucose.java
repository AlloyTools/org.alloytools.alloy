/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package org.alloytools.solvers.natv.glucose;

import kodkod.engine.satlab.NativeSolver;

/**
 * Java wrapper for the Glucose solver by G. Audemard and L. Simon. ative
 *
 * @author Emina Torlak
 */
public final class Glucose extends NativeSolver {

    /**
     * Constructs a new Glucose wrapper.
     */
    public Glucose() {
        super(NativeSolver.make("Glucose", Glucose::make));
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Glucose";
    }

    /**
     * Returns a pointer to an instance of the glucose solver.
     *
     * @return a pointer to an instance of the glucose solver.
     */
    private static native long make();

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#free(long)
     */
    @Override
    public native void free(long peer);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#addVariables(long, int)
     */
    @Override
    public native void addVariables(long peer, int numVariables);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#addClause(long, int[])
     */
    @Override
    public native boolean addClause(long peer, int[] lits);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#solve(long)
     */
    @Override
    public native boolean solve(long peer);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#valueOf(long, int)
     */
    @Override
    public native boolean valueOf(long peer, int literal);

}
