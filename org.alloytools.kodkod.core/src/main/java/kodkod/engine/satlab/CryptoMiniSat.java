/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
package kodkod.engine.satlab;

/**
 * Java wrapper for the CryptoMiniSat solver by Mate Soos.
 *
 * @author Emina Torlak
 */
final class CryptoMiniSat extends NativeSolver {

    /**
     * Constructs a new MiniSAT wrapper.
     */
    public CryptoMiniSat() {
        super(make());
        // TODO Auto-generated constructor stub
    }

    static {
        loadLibrary(CryptoMiniSat.class);
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "CryptoMiniSat";
    }

    /**
     * Returns a pointer to an instance of MiniSAT.
     *
     * @return a pointer to an instance of minisat.
     */
    private static native long make();

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#free(long)
     */
    @Override
    native void free(long peer);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#addVariables(long, int)
     */
    @Override
    native void addVariables(long peer, int numVariables);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#addClause(long, int[])
     */
    @Override
    native boolean addClause(long peer, int[] lits);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#solve(long)
     */
    @Override
    native boolean solve(long peer);

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.NativeSolver#valueOf(long, int)
     */
    @Override
    native boolean valueOf(long peer, int literal);

}
