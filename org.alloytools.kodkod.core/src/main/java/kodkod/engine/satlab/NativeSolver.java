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

import java.io.File;

import org.alloytools.nativecode.util.NativeCode;

/**
 * A skeleton implementation of a wrapper for a sat solver accessed through JNI.
 *
 * @author Emina Torlak
 */
abstract class NativeSolver implements SATSolver {

    /**
     * The memory address of the native instance wrapped by this wrapper.
     */
    private long    peer;
    private Boolean sat;
    private int     clauses, vars;

    /**
     * Constructs a new wrapper for the given instance of the native solver.
     */
    NativeSolver(long peer) {
        this.peer = peer;
        this.clauses = this.vars = 0;
        this.sat = null;
        // System.out.println("created " + peer);
    }

    /**
     * Loads the JNI library for the given class. It first attempts to load the
     * library named library.getSimpleName().toLowerCase(). If that fails, it
     * attempts to load library.getSimpleName().toLowerCase()+suffix where suffix
     * ranges over the path-separator delimited list obtained by calling
     * System.getProperty("kodkod." + library.getSimpleName().toLowerCase()).
     */
    static void loadLibrary(Class< ? extends NativeSolver> library) {
        final String name = library.getSimpleName().toLowerCase();
        try {
            System.loadLibrary(name);
        } catch (UnsatisfiedLinkError e) {
            final String versions = System.getProperty("kodkod." + name);
            if (versions != null) {
                for (String suffix : versions.split(File.pathSeparator)) {
                    try {
                        System.loadLibrary(name + suffix);
                        return;
                    } catch (UnsatisfiedLinkError e1) {}
                }
            }

            if (NativeCode.loadlibrary(null, name))
                return;

            throw new UnsatisfiedLinkError("Could not load the library " + System.mapLibraryName(name) + " or any of its variants:" + e.getMessage());
        }

    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
     */
    @Override
    public final int numberOfVariables() {
        return vars;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
     */
    @Override
    public final int numberOfClauses() {
        return clauses;
    }

    /**
     * Adjusts the internal clause count so that the next call to
     * {@linkplain #numberOfClauses()} will return the given value.
     *
     * @requires clauseCount >= 0
     * @ensures adjusts the internal clause so that the next call to
     *          {@linkplain #numberOfClauses()} will return the given value.
     */
    final void adjustClauseCount(int clauseCount) {
        assert clauseCount >= 0;
        clauses = clauseCount;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#addVariables(int)
     * @see #addVariables(long, int)
     */
    @Override
    public final void addVariables(int numVars) {
        if (numVars < 0)
            throw new IllegalArgumentException("vars < 0: " + numVars);
        else if (numVars > 0) {
            vars += numVars;
            addVariables(peer, numVars);
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#addClause(int[])
     * @see #addClause(long, int[])
     */
    @Override
    public final boolean addClause(int[] lits) {
        if (addClause(peer, lits)) {
            // for(int i : lits) {
            // System.out.print(i + " ");
            // }
            // System.out.println(0);
            clauses++;
            return true;
        }
        return false;
    }

    /**
     * Returns a pointer to the C++ peer class (the native instance wrapped by this
     * object).
     *
     * @return a pointer to the C++ peer class (the native instance wrapped by this
     *         object).
     */
    final long peer() {
        return peer;
    }

    /**
     * Returns the current sat of the solver.
     *
     * @return null if the sat is unknown, TRUE if the last call to solve() yielded
     *         SAT, and FALSE if the last call to solve() yielded UNSAT.
     */
    final Boolean status() {
        return sat;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#solve()
     * @see #solve(long)
     */
    @Override
    public final boolean solve() {
        if (sat == Boolean.FALSE)
            return sat;
        else
            return (sat = Boolean.valueOf(solve(peer)));
    }

    /**
     * Throws an IllegalArgumentException if variable !in this.variables. Otherwise
     * does nothing.
     *
     * @throws IllegalArgumentException variable !in this.variables
     */
    final void validateVariable(int variable) {
        if (variable < 1 || variable > vars)
            throw new IllegalArgumentException(variable + " !in [1.." + vars + "]");
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#valueOf(int)
     */
    @Override
    public final boolean valueOf(int variable) {
        if (sat != Boolean.TRUE)
            throw new IllegalStateException();
        validateVariable(variable);
        return valueOf(peer, variable);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#free()
     */
    @Override
    public synchronized final void free() {
        if (peer != 0) {
            // System.out.println("freeing " + peer + " " + getClass());
            free(peer);
            sat = Boolean.FALSE;
            peer = 0;
        } // already freed
    }

    /**
     * Releases the resources used by this native solver.
     */
    @Override
    protected final void finalize() throws Throwable {
        super.finalize();
        free();
    }

    /**
     * Releases the resources associated with the native solver at the given memory
     * address. This method must be called when the object holding the given
     * reference goes out of scope to avoid memory leaks.
     *
     * @ensures releases the resources associated with the given native peer
     */
    abstract void free(long peer);

    /**
     * Adds the specified number of variables to the given native peer.
     *
     * @ensures increases the vocabulary of the given native peer by the specified
     *          number of variables
     */
    abstract void addVariables(long peer, int numVariables);

    /**
     * Ensures that the given native peer logically contains the specified clause
     * and returns true if the solver's clause database changed as a result of the
     * call.
     *
     * @requires all i: [0..lits.length) | abs(lits[i]) in this.variables
     * @requires all disj i,j: [0..lits.length) | abs(lits[i]) != abs(lits[j])
     * @ensures ensures that the given native peer logically contains the specified
     *          clause
     * @return true if the peer's clause database changed as a result of the call; a
     *         negative integer if not.
     */
    abstract boolean addClause(long peer, int[] lits);

    /**
     * Calls the solve method on the given native peer.
     *
     * @return true if the clauses in the solver are SAT; otherwise returns false.
     */
    abstract boolean solve(long peer);

    /**
     * Returns the assignment for the given literal by the specified native peer
     *
     * @requires the last call to {@link #solve(long) solve(peer)} returned
     *           SATISFIABLE
     * @return the assignment for the given literal
     */
    abstract boolean valueOf(long peer, int literal);

}
