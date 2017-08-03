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
 * Provides an interface to a SAT solver.
 * 
 * @specfield variables: set [1..)
 * @specfield clauses: set Clause
 * @invariant all i: [2..) | i in variables => i-1 in variables
 * @invariant all c: clauses | all lit: c.literals | lit in variables || -lit in variables
 * @invariant all c: clauses | all disj i,j: c.literals | abs(i) != abs(j)
 * @author Emina Torlak
 */
public interface SATSolver {
	
	/**
	 * Returns the size of this solver's vocabulary.
	 * @return #this.variables
	 */
	public abstract int numberOfVariables();
	
	/**
	 * Returns the number of clauses in this solver.
	 * @return #this.clauses
	 */
	public abstract int numberOfClauses();
	
	/**
	 * Adds the specified number of new variables
	 * to the solver's vocabulary.  The behavior of this 
	 * method is undefined if it is called after this.solve()
	 * has returned <tt>false</tt>.
	 * @requires numVars >= 0
	 * @ensures this.variables' = [1..#this.variables + numVars]
	 * @throws IllegalArgumentException  numVars < 0
	 */
	public abstract void addVariables(int numVars);
	
	/**
	 * Ensures that this solver logically contains the given 
	 * clause, and returns true if this.clauses changed as a 
	 * result of the call. No reference to the specified array 
	 * is kept, so it can be reused.  <b>The contents of the array may, 
	 * however, be modified.</b>  It is the client's responsibility to 
	 * ensure that no literals in the given array are repeated, or that
	 * both a literal and its negation are present.  The behavior of this 
	 * method is undefined if it is called after this.solve()
	 * has returned <tt>false</tt>.
	 * @requires all i: [0..lits.length) | abs(lits[i]) in this.variables 
	 * @requires all disj i,j: [0..lits.length) | abs(lits[i]) != abs(lits[j])
	 * @ensures [[this.clauses']] = ([[this.clauses]] and [[lits]])
	 * @return #this.clauses' > #this.clauses
	 * @throws NullPointerException  lits = null
	 */
	public abstract boolean addClause(int[] lits);
	
	/**
	 * Returns true if there is a satisfying assignment for this.clauses.
	 * Otherwise returns false.  If this.clauses are satisfiable, the 
	 * satisfying assignment for a given variable
	 *  can be obtained by calling {@link #valueOf(int)}.
	 * If the satisfiability of this.clauses cannot be determined within
	 * the given number of seconds, a TimeoutException is thrown.
	 * @return true if this.clauses are satisfiable; otherwise false.
	 * @throws SATAbortedException - the call to solve was cancelled or
	 * could not terminate normally.
	 */
	public abstract boolean solve() throws SATAbortedException;
	
	/**
	 * Returns the boolean value assigned to the given variable by the
	 * last successful call to {@link #solve()}. 
	 * @requires {@link #solve() } has been called and the 
	 * outcome of the last call was <code>true</code>.  
	 * @return the boolean value assigned to the given variable by the
	 * last successful call to {@link #solve()}. 
	 * @throws IllegalArgumentException  variable !in this.variables
	 * @throws IllegalStateException  {@link #solve() } has not been called or the 
	 * outcome of the last call was not <code>true</code>.
	 */
	public abstract boolean valueOf(int variable);
	
	/**
	 * Frees the memory used by this solver.  Once free() is called,
	 * all subsequent calls to methods other than free() may fail.  
	 * @ensures frees the memory used by this solver
	 */
	public abstract void free();
	
}
