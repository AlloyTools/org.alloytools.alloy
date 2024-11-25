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
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import kodkod.solvers.api.NativeCode;

/**
 * A skeleton implementation of a wrapper for a sat solver accessed through JNI.
 * 
 * @author Emina Torlak
 */
public abstract class NativeSolver implements SATSolver {
	static Logger logger = LoggerFactory.getLogger(NativeSolver.class);

	final static AtomicLong ID = new AtomicLong(1000);

	private final long id = ID.incrementAndGet();
	private final long peer;
	private final AtomicBoolean freed = new AtomicBoolean(false);
	private Boolean sat;
	private int clauses, vars;

	/**
	 * Constructs a new wrapper for the given instance of the native solver.
	 */
	protected NativeSolver(long peer) {
		this.peer = peer;
		this.clauses = this.vars = 0;
		this.sat = null;
		logger.debug("created native solver {} {}", getClass().getSimpleName(), peer);
	}

	/**
	 * Loads the JNI library for the given class. It first attempts to load the
	 * library named library.getSimpleName().toLowerCase(). If that fails, it
	 * attempts to load library.getSimpleName().toLowerCase()+suffix where suffix
	 * ranges over the path-separator delimited list obtained by calling
	 * System.getProperty("kodkod." + library.getSimpleName().toLowerCase()).
	 */
	protected static void loadLibrary(Class<? extends NativeSolver> library) {
		final String name = library.getSimpleName().toLowerCase();
		try {
			try {
				System.loadLibrary(name);
				logger.debug("loaded library {} for class {}", name, library.getSimpleName());
			} catch (UnsatisfiedLinkError e) {

				final String versions = System.getProperty("kodkod." + name);
				if (versions != null) {
					logger.debug("library {} for class {} has system property kodkod.{} set to {}", name,
							library.getSimpleName(), name, versions);
					for (String suffix : versions.split(File.pathSeparator)) {
						try {
							System.loadLibrary(name + suffix);
							logger.debug("library {} for class {} mapped to {} loads", name, library.getSimpleName(),
									name + suffix);
							return;
						} catch (UnsatisfiedLinkError e1) {
						}
					}
				}
				logger.debug("could not load library {} for class {}", name, library.getSimpleName());
				throw new UnsatisfiedLinkError("Could not load the library " + System.mapLibraryName(name)
						+ " or any of its variants:" + e.getMessage());
			}
		} catch (Throwable t) {
			logger.error("could not find native library {} for class {}, thrown error is {}. Embedded natives are {}",
					name, library.getSimpleName(), t.getMessage(), NativeCode.platform.embedded());
			throw t;
		}
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public final int numberOfVariables() {
		valid();
		return vars;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public final int numberOfClauses() {
		valid();
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
	public void adjustClauseCount(int clauseCount) {
		valid();
		assert clauseCount >= 0;
		clauses = clauseCount;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 * @see #addVariables(long, int)
	 */
	public final void addVariables(int numVars) {
		valid();
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
	public final boolean addClause(int[] lits) {
		valid();
		if (addClause(peer, lits)) {
//			for(int i : lits) {
//				System.out.print(i + " ");
//			}
//			System.out.println(0);
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
	public final long peer() {
		valid();
		return peer;
	}

	/**
	 * Returns the current sat of the solver.
	 * 
	 * @return null if the sat is unknown, TRUE if the last call to solve() yielded
	 *         SAT, and FALSE if the last call to solve() yielded UNSAT.
	 */
	public final Boolean status() {
		valid();
		return sat;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 * @see #solve(long)
	 */
	public final boolean solve() {
		valid();
		if (sat == Boolean.FALSE) {
			logger.debug("[{}] already false??", id);
			return sat;
		}

		logger.debug("[{}] solving in JNI peer. vars={}, clauses, sat={}", id, vars, clauses, sat);
		try {
			sat = solve(peer);
			logger.debug("[{}] solved sat={}", id, vars, clauses, sat);
			return sat;
		} catch (Exception e) {
			logger.error("[{}] error failed to solve in native JNI solver {}", id, e, e);
			throw e;
		}
	}

	/**
	 * Throws an IllegalArgumentException if variable !in this.variables. Otherwise
	 * does nothing.
	 * 
	 * @throws IllegalArgumentException variable !in this.variables
	 */
	public void validateVariable(int variable) {
		valid();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars + "]");
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	public final boolean valueOf(int variable) {
		valid();
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
	public synchronized final void free() {
		if (freed.getAndSet(true) == false) {
			logger.debug("[{}] free {} {}", id, getClass().getSimpleName(), peer);
			free(peer);
		} else {
			logger.warn("[{}] free called multiple times {}", id, getClass().getSimpleName());
		}
	}

	void valid() {
		if ( freed.get()) {
			throw new IllegalStateException("this native solver is already freed: " + id + " " + getClass().getSimpleName());
		}
	}
	/**
	 * Releases the resources used by this native solver.
	 * @deprecated
	 */
	@Deprecated
	protected final void finalize() throws Throwable {
		super.finalize();
		if (freed.getAndSet(true) == false) {
			logger.warn("[{}] finalize called {}", id, getClass().getSimpleName());
			free();			
		}
	}

	/**
	 * Releases the resources associated with the native solver at the given memory
	 * address. This method must be called when the object holding the given
	 * reference goes out of scope to avoid memory leaks.
	 * 
	 * @ensures releases the resources associated with the given native peer
	 */
	public abstract void free(long peer);

	/**
	 * Adds the specified number of variables to the given native peer.
	 * 
	 * @ensures increases the vocabulary of the given native peer by the specified
	 *          number of variables
	 */
	public abstract void addVariables(long peer, int numVariables);

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
	public abstract boolean addClause(long peer, int[] lits);

	/**
	 * Calls the solve method on the given native peer.
	 * 
	 * @return true if the clauses in the solver are SAT; otherwise returns false.
	 */
	public abstract boolean solve(long peer);

	/**
	 * Returns the assignment for the given literal by the specified native peer
	 * 
	 * @requires the last call to {@link #solve(long) solve(peer)} returned
	 *           SATISFIABLE
	 * @return the assignment for the given literal
	 */
	public abstract boolean valueOf(long peer, int literal);

	public static long make(String type, Supplier<Long> make) {
		try {
			logger.debug("trying to 'make' JNI peer {}", type);
			long peer = make.get();
			logger.debug("made JNI peer {}", peer);
			return peer;
		} catch (Throwable t) {
			logger.error("failed to make JNI peer {}", type, t, t);
			throw t;
		}
	}

}
