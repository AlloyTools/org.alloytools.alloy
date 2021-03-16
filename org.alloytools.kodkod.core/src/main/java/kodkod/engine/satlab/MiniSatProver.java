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

import java.util.Iterator;

import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

/**
 * Java wrapper for the MiniSat solver with proof logging. MiniSat is developed
 * by Niklas E&eacute;n and Niklas S&ouml;rensson.
 *
 * @author Emina Torlak
 */
final class MiniSatProver extends NativeSolver implements SATProver {

    private LazyTrace proof;

    /**
     * Constructs a new MiniSat prover wrapper.
     */
    MiniSatProver() {
        super(make());
        proof = null;
    }

    static {
        loadLibrary(MiniSatProver.class);
    }

    /**
     * Returns a subset of the given trivial trace that consists only of axioms. A
     * trace is trivial iff its last clause is an empty clause. This means that the
     * empty axiom was added to the solver via {@linkplain #addClause(int[])}, so no
     * resolution was necessary to reach the conflict. The empty axiom is always the
     * last clause in the trace.
     *
     * @requires trace[trace.length].length = 0
     * @return a subset of the given trivial trace that consists only of axioms
     */
    private int[][] formatTrivial(int[][] trace) {
        final int length = trace.length;
        final int empty = length - 1;
        final IntSet axioms = new IntBitSet(length);
        axioms.add(empty);
        final int numVars = numberOfVariables();
        for (int i = 0; i < empty; i++) {
            int[] clause = trace[i];
            if (clause[0] <= numVars) {
                axioms.add(i);
            }
        }
        if (axioms.size() == length) {
            return trace;
        }
        final int[][] axiomClauses = new int[axioms.size()][];
        final IntIterator itr = axioms.iterator();
        for (int i = 0; itr.hasNext(); i++) {
            axiomClauses[i] = trace[itr.next()];
        }
        return axiomClauses;
    }

    /**
     * Modifies the given raw trace so that it conforms to the specification of
     * {@linkplain LazyTrace#LazyTrace(int[][], int)}, if the array contains no null
     * entries, and to the specfication of
     * {@linkplain LazyTrace#LazyTrace(LazyTrace, IntSet, int[][])} otherwise.
     *
     * @ensures modifies the trace so that it conforms to the specification of one
     *          of the LazyTrace constructors.
     * @return trace
     */
    private int[][] format(int[][] trace) {
        final int length = trace.length;
        final IntSet resolvents = new IntBitSet(length);
        final int offset = numberOfVariables() + 1;
        for (int i = 0; i < length; i++) {
            int[] clause = trace[i];
            if (clause != null && clause[0] >= offset) {
                clause[0] -= offset;
                resolvents.add(i);
            }
        }

        final int axioms = length - resolvents.size();
        if (resolvents.min() < axioms) {
            final int[] position = new int[length];
            for (int i = 0, axiomIndex = 0, resolventIndex = axioms; i < length; i++) {
                if (resolvents.contains(i)) {
                    position[i] = resolventIndex++;
                    int[] resolvent = trace[i];
                    for (int j = 0, resLength = resolvent.length; j < resLength; j++) {
                        resolvent[j] = position[resolvent[j]];
                    }
                } else {
                    position[i] = axiomIndex++;
                }
            }

            for (IntIterator itr = resolvents.iterator(length, 0); itr.hasNext();) {
                int i = itr.next();
                int pos = position[i];
                if (i == pos)
                    continue; // correctly positioned, do nothing
                int[] resolvent = trace[i];
                System.arraycopy(trace, i + 1, trace, i, pos - i);
                trace[pos] = resolvent;
            }
        }
        assert axioms == numberOfClauses();
        return trace;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATProver#proof()
     */
    @Override
    public ResolutionTrace proof() {
        if (!Boolean.FALSE.equals(status()))
            throw new IllegalStateException();
        if (proof == null) {
            final int[][] trace = trace(peer(), true);
            free();
            // if the empty axiom was added to the solver, that axiom will be
            // the last clause in the trace, and it will form its own minimal
            // unsat core.
            // System.out.println(Arrays.deepToString(trace));
            if (trace[trace.length - 1].length == 0) {
                proof = new LazyTrace(formatTrivial(trace), numberOfClauses());
            } else {
                proof = new LazyTrace(format(trace), numberOfClauses());
            }
        }
        return proof;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATProver#reduce(kodkod.engine.satlab.ReductionStrategy)
     */
    @Override
    public void reduce(ReductionStrategy strategy) {
        proof();
        if (proof.resolvents().isEmpty()) {
            return; // nothing to minimize; we had an empty axiom added to the
                   // solver's database
        }

        for (IntSet next = strategy.next(proof); !next.isEmpty(); next = strategy.next(proof)) {
            long prover = make();
            addVariables(prover, numberOfVariables());

            for (Iterator<Clause> itr = proof.iterator(next); itr.hasNext();) {
                Clause c = itr.next();
                if (!addClause(prover, c.toArray())) {
                    throw new AssertionError("could not add non-redundant clause: " + c);
                }
            }

            if (!solve(prover)) {
                adjustClauseCount(next.size());
                int[][] trace = trace(prover, false);
                free(prover);
                proof = new LazyTrace(proof, next, format(trace));
            } else {
                free(prover);
            }
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "MiniSatProver";
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

    /**
     * Returns an array of arrays that encodes the most recently generated
     * resolution trace. The resolution trace is encoded as follows. Let R be the
     * returned array. For all 0 <= i < trace.length such that R[i][0] >
     * this.numberOfVariables(), the array R[i] encodes a resolvent clause. In
     * particular, (R[i][0] - this.numberOfVariables() - 1) < i is the index of the
     * 0th antecedent of R[i] in R; for each 0 < j < R[i].length, R[i][j] < i and
     * R[i][j] is the index of the jth antecedent of R[i] in R. For all 0 <= i <
     * trace.length-1 such that R[i][0] <= this.numberOfVariables(), R[i] contains
     * the literals of the ith axiom, sorted in the increasing order of absolute
     * values, if recordAxioms is true; otherwise R[i] is null.
     *
     * @return an array of arrays that encodes the most recently generated
     *         resolution trace
     */
    native int[][] trace(long peer, boolean recordAxioms);
}
