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
package kodkod.engine.satlab;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.stream.Collectors;

import org.slf4j.LoggerFactory;

import kodkod.engine.config.ExtendedOptions;
import kodkod.solvers.LightSat4JRef;
import kodkod.solvers.PMaxSAT4JRef;
import kodkod.solvers.SAT4JRef;
import kodkod.solvers.api.NativeCode;

/**
 * Alloy Native code
 * 
 * The actual SAT solvers are abstracted through a SATFactory, who can create
 * instances of SATSolvers.
 * 
 * SATFactory objects are used to indicate what solver should be used. They can
 * be used as identity for the solver. That is, these objects can be used to
 * provide dynamic list of available solvers. Therefore, a SATFactory must
 * always return the same type of solver. Alloy serializes the SATFactory when
 * it creates a process to run the solver in.
 *
 * There are a number of static methods that can provide the list of standard
 * SATFactorys. This the {@link SATFactory#getAllSolvers()} returns a list of
 * all SATFactory available. Since numerous solvers depend on external and
 * native code, these are generally filters in {@link #getSolvers()}. The
 * {@link #find(String)} and {@link #get(String)} methods provide direct access
 * to get/find a SATFactory.
 * 
 * There are a number of ways a SATFactory can be included in the
 * {@link #getAllSolvers()}.
 * 
 * <ul>
 * <li>Using the Service Loader. This requires a JAR on the class path to have a
 * META-INF/services/kodkod.engine.satlab.SATFactory file. This file can contain
 * a list of classes that must implement/extend the SATFactory.
 * <li>The {@link #extensions} variables is a list that will always be included.
 * Different parts of the system can add a SATFactory at startup.
 * </ul>
 */
public abstract class SATFactory implements Serializable, Comparable<SATFactory> {
	private final static org.slf4j.Logger log = LoggerFactory.getLogger(SATFactory.class);
	private static final long serialVersionUID = 1L;
	protected static final String[] EMPTY = new String[0];

	/**
	 * Any SATFactory objects added to this list will be included in the
	 * {@link #getAllSolvers()} list. Can be used to add experimental or custom
	 * solvers.
	 */
	public static List<SATFactory> extensions = new ArrayList<>();
	public static final SATFactory DEFAULT = SAT4JRef.INSTANCE;

	static {
		extensions.add(DEFAULT);
		extensions.add(LightSat4JRef.INSTANCE);
		extensions.add(PMaxSAT4JRef.INSTANCE);
	}

	protected SATFactory() {
	}

	/**
	 * Return the identity of this solver. No two SATFactory objects should have the
	 * same id.
	 */
	public abstract String id();

	/**
	 * Check if the SATSolver is available. Return null if so, otherwise a reason
	 * why it is not available is returned.
	 */

	public String check() {
		if (!isPresent())
			return "cannot be found";

		if ( isTransformer())
		    return "";
		
		SATSolver solver = null;
		try {
			solver = instance();
			solver.addVariables(1);
			solver.addClause(new int[] { 1 });
			if (solver.solve())
				return null;
			;
			return "could not solve trivial problem";
		} catch (Exception t) {
			return t.toString();
		} catch (UnsatisfiedLinkError t) {
			return "unsatisfied linking: " + t.getMessage();
		} finally {
			if (solver != null) {
				solver.free();
			}
		}

	}

	/**
	 * Returns an instance of a SATSolver produced by this factory.
	 * 
	 * @return a SATSolver instance
	 */
	public SATSolver instance() {
		throw new UnsupportedOperationException(this + " is not a SATFactory that can create instances");
	}

	/**
	 * Returns true if the solvers returned by this.instance() are {@link SATProver
	 * SATProvers}. Otherwise returns false.
	 * 
	 * @return true if the solvers returned by this.instance() are {@link SATProver
	 *         SATProvers}. Otherwise returns false.
	 */
	public boolean prover() {
		return false;
	}

	/**
	 * Returns true if the solvers returned by this.instance() are incremental; i.e.
	 * if clauses/variables can be added to the solver between multiple calls to
	 * solve().
	 * 
	 * @return true if the solvers returned by this.instance() are incremental
	 */
	public boolean incremental() {
		return false;
	}

	/**
	 * Returns true if the solvers returned by this.instance() are unbounded.
	 * 
	 * @return true if the solvers returned by this.instance() are incremental
	 */
	public boolean unbounded() {
		return false;
	}

	/**
	 * Returns true if the solvers returned by this.instance() are Max-SAT, i.e.,
	 * soft clauses and weights can added to the solver.
	 * 
	 * @return true if the solvers returned by this.instance() are Max-SAT
	 */
	public boolean maxsat() {
		return false;
	}

	/**
	 * Return a human readable description of this solver.
	 */
	public Optional<String> getDescription() {
		return Optional.empty();
	};

	/**
	 * Return a list of all SATFactory that are found on this platform.
	 */
	public static List<SATFactory> getSolvers() {
		return getAllSolvers().stream().filter(SATFactory::isPresent).collect(Collectors.toList());
	}

	/**
	 * Return all solvers on this platform in a sorted list by {@link #id()}. This
	 * contains:
	 * <ul>
	 * <li>the SATFactory's in {@link #extensions}
	 * <li>{@link #DEFAULT}
	 * <li>{@link #KK}
	 * <li>{@link #CNF}
	 * <li>All SATFactory's that can be found with the Service Loader.
	 * </ul>
	 */
	public static List<SATFactory> getAllSolvers() {
		ServiceLoader<SATFactory> loader = ServiceLoader.load(SATFactory.class, SATFactory.class.getClassLoader());
		List<SATFactory> result = new ArrayList<>(extensions);
		Iterator<SATFactory> iterator = loader.iterator();
		while (iterator.hasNext())
			try {
				SATFactory r = iterator.next();
				result.add(r);
			} catch (Throwable e) {
				log.error("failure in loading solvers {}", e);
				return Collections.emptyList();
			}
		Collections.sort(result);
		return result;
	}

	/**
	 * Check if the SATFactory is present
	 */
	public boolean isPresent() {
	    if ( isTransformer())
	        return true;
	    
		try {
			instance();
			for (String library : getLibraries()) {
				if (!NativeCode.platform.getLibrary(library).isPresent())
					return false;
			}
			for (String executable : getExecutables()) {
				if (!NativeCode.platform.getExecutable(executable).isPresent())
					return false;
			}
			return true;
		} catch (java.lang.UnsatisfiedLinkError e) {
			log.debug("lib {} gave error {}", id(), e.getMessage());
		} catch (Exception e) {
			log.debug("not present {}", id());
		}
		return false;
	}

	/**
	 * Get a list of executable names. These executable names must be generic,
	 * without suffix. For Unix/MacOS this is just the name of the executable. For
	 * windows, it must be without .exe.
	 */
	public String[] getExecutables() {
		return EMPTY;
	}

	/**
	 * Get a list of library names. These library names must be generic, without
	 * suffix. For Unix this is libNAME.so, for MacOS this is libNAME.dylib, and for
	 * windows this is NAME.dll.
	 */
	public String[] getLibraries() {
		return EMPTY;
	}

	/**
	 * This must be called before the solver is used so that the solver can
	 * influence the options.
	 * 
	 * @param options the options
	 */
	public SATFactory doOptions(ExtendedOptions options) {
		return this;
	}

	/**
	 * Find a SAT Factory by name.
	 * 
	 * @param solver the solver name
	 */
	public static Optional<SATFactory> find(String solver) {
		return getSolvers().stream().filter(s -> s.id().equalsIgnoreCase(solver)).findFirst();
	}

	/**
	 * Get a SAT Factory by name. If not found, throw an IllegalArgumentException.
	 * 
	 * @param solver the solver name
	 */
	public static SATFactory get(String solver) {
		return find(solver).orElseThrow(
				() -> new IllegalArgumentException("no solver " + solver + ", available are " + getSolvers()));
	}

	@Override
	public int compareTo(SATFactory o) {
		return id().compareTo(o.id());
	}

	/**
	 * Two SATFactory objects are equal if their id is equal.
	 */
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof SATFactory))
			return false;

		return id().equals(((SATFactory) o).id());
	}

	/**
	 * Two SATFactory objects are equal if their id is equal.
	 */
	@Override
	public int hashCode() {
		return id().hashCode();
	}

	public String toString() {
		return name();
	}

	public abstract String type();

	public String attributes() {
		List<String> attrs = new ArrayList<>();
		if (incremental())
			attrs.add("incr");
		if (maxsat())
			attrs.add("max");
		if (prover())
			attrs.add("prover");

		return attrs.stream().collect(Collectors.joining(","));
	}

	public String name() {
		return id();
	}

	public boolean isTransformer() {
		return false;
	}

	
}
