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
 * Provides an interface to a SAT solver that can generate proofs of
 * unsatisfiability.
 *
 * @specfield variables: set [1..)
 * @specfield clauses: set Clause
 * @specfield resolvents: set Clause
 * @invariant all i: [2..) | i in variables => i-1 in variables
 * @invariant all c: clauses + resolvents | all lit: c.lits | lit in variables
 *            || -lit in variables
 * @invariant all c: clauses + resolvents | all disj i,j: c.lits | abs(i) !=
 *            abs(j)
 * @author Emina Torlak
 */
public interface SATProver extends SATSolver {

    /**
     * Returns a resolution-based proof of unsatisfiability of this.clauses.
     *
     * @requires {@link SATSolver#solve()} has been called, and it returned false
     * @return { t: ResolutionTrace | t.prover = this }
     * @throws IllegalStateException {@link SATSolver#solve()} has not been called,
     *             or the last call to {@link SATSolver#solve()} returned true
     */
    public ResolutionTrace proof();

    /**
     * Uses the given reduction strategy to remove irrelevant clauses from the set
     * of unsatisfiable clauses stored in this prover. A clause c is irrelevant iff
     * this.clauses - c is unsatisfiable. The removal algorithm works as follows:
     *
     * <pre>
     * for (IntSet next = strategy.next(this.proof()); !next.isEmpty(); next = strategy.next(this.proof())) {
     *  let oldClauses = this.clauses, oldResolvents = this.resolvents
     *  clear this.clauses
     *  clear this.resolvents
     *  for(Clause c : this.proof().elts[next]) {
     *    if (no c.antecedents)
     *      add c to this.clauses
     *    else
     *      add c to this.resolvents
     *  }
     *  if (this.solve()) {
     *   this.clauses = oldClauses
     *   this.resolvents = oldResolvents
     *  }
     * }
     * </pre>
     *
     * @requires {@link SATSolver#solve()} has been called, and it returned false
     * @ensures modifies this.clauses and this.resolvents according to the algorithm
     *          described above
     * @throws IllegalStateException {@link SATSolver#solve()} has not been called,
     *             or the last call to {@link SATSolver#solve()} returned true
     * @see ReductionStrategy
     */
    public void reduce(ReductionStrategy strategy);

}
