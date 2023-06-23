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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.pb.IPBSolver;
import org.sat4j.pb.PseudoOptDecorator;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IOptimizationProblem;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * A wrapper class that provides access to the basic functionality of the
 * PMax-SAT SAT4J solver (org.sat4j.pb.IPBSolver), adapted from
 * {@link kodkod.engine.satlab.SAT4J}.
 * 
 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model finding
 */
final public class PMaxSAT4J implements WTargetSATSolver { 
	private WeightedMaxSatDecorator solver;
	private IOptimizationProblem optproblem;
	private ReadOnlyIVecInt wrapper;
	private Boolean sat;
	private int vars, clauses;
	private Set<int[]> hardclauses = new HashSet<int[]>();  
	private Map<Integer,Integer> softclauses = new HashMap<Integer,Integer>();
	/**
	 * Constructs a wrapper for the given instance of ISolver.
	 * 
	 * @throws NullPointerException
	 *             solver = null
	 */
	PMaxSAT4J(IPBSolver solver) {
		if (solver == null)
			throw new NullPointerException("solver");
		this.solver = new WeightedMaxSatDecorator(solver);
		this.wrapper = new ReadOnlyIVecInt();
		this.sat = null;
		this.vars = clauses = 0;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public int numberOfVariables() {
		return vars;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public int numberOfClauses() {
		return clauses;
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#numberOfTargets()
	 */
	public int numberOfTargets() {
		return softclauses.size();
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 */
	public void addVariables(int numVars) {
		if (numVars < 0)
			throw new IllegalArgumentException("numVars < 0: " + numVars);
		else if (numVars > 0)
			vars += numVars;
	}

	/**
	 * {@inheritDoc}
	 * Clauses are added to a buffer instead of directly to the SAT because it 
	 * must be reconstructed at each iteration to update the targets.
	 * @see kodkod.engine.satlab.SATSolver#addClause(int[])
	 */
	public boolean addClause(int[] lits) {
		clauses++;
		hardclauses.add(lits.clone());
		return true;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#addTarget(int)
	 */
	public boolean addTarget(int lit) {
		return addWeight(lit, 1);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#addWeight(int,int)
	 */	
	public boolean addWeight(int lit, int weight) {
		softclauses.put(lit,weight);
		clauses++;
		return true;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */

	public boolean solve() {
		solver.reset();
		solver.setTopWeight(BigInteger.valueOf(10000));
		solver.setExpectedNumberOfClauses(clauses);
		solver.newVar(vars);
		solver.setTimeout(1000);
		try {
			// add the target variables as soft clauses
			for (Integer x : softclauses.keySet()) 
				solver.addSoftClause(softclauses.get(x),wrapper.wrap(new int[] { x }));
			// add the problem variables as hard clauses
			for (int[] x : hardclauses) 
				solver.addHardClause(wrapper.wrap(x));
		} catch (ContradictionException e) {
			sat = Boolean.FALSE;
		}		

		if (!Boolean.FALSE.equals(sat)) {
			boolean isSatisfiable = false;
			try {
				optproblem = new PseudoOptDecorator(solver);

				while (optproblem.admitABetterSolution()) {
					optproblem.discardCurrentSolution();
					isSatisfiable = true;
				}

				if (isSatisfiable) {
					sat = true;
					return true;
				} else {
					return false;
				}
			} catch (ContradictionException ex) {
				sat = true;
				return true;
			} catch (org.sat4j.specs.TimeoutException e) {
				throw new RuntimeException("timed out");
			}
		}

		return sat;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	public final boolean valueOf(int variable) {
		if (!Boolean.TRUE.equals(sat))
			throw new IllegalStateException();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars
					+ "]");
		return optproblem.model(variable);
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.satlab.SATSolver#free()
	 */
	public synchronized final void free() {
		solver.reset();
		optproblem = null;
		solver = null;
	}

	protected final void finalize() throws Throwable {
		super.finalize();
		free();
	}

	/**
	 * A wrapper for an int array that provides read-only access to the array
	 * via the IVecInt interface.
	 * 
	 * @author Emina Torlak
	 */
	private static final class ReadOnlyIVecInt implements IVecInt {
		private static final long serialVersionUID = -7689441271777278043L;
		private int[] vec;

		/**
		 * Sets this.vec to the given vector and returns this.
		 */
		IVecInt wrap(int[] vec) {
			this.vec = vec;
			return this;
		}

		public int size() {
			return vec.length;
		}

		public boolean isEmpty() {
			return size() == 0;
		}

		public int unsafeGet(int arg0) {
			return vec[arg0];
		}

		public int last() {
			return vec[vec.length - 1];
		}

		public int[] toArray() {
			return vec;
		}

		public int get(int arg0) {
			if (arg0 < 0 || arg0 >= vec.length)
				throw new IndexOutOfBoundsException("arg0: " + arg0);
			return vec[arg0];
		}

		public boolean contains(int arg0) {
			final int[] workArray = vec; // faster access
			for (int i : workArray) {
				if (i == arg0)
					return true;
			}
			return false;
		}

		public void copyTo(IVecInt arg0) {
			int argLength = arg0.size();
			final int[] workArray = vec; // faster access
			arg0.ensure(argLength + workArray.length);
			for (int i : workArray) {
				arg0.set(argLength++, i);
			}
		}

		public void copyTo(int[] arg0) {
			assert arg0.length >= vec.length;
			System.arraycopy(vec, 0, arg0, 0, vec.length);
		}

		public IteratorInt iterator() {
			return new IteratorInt() {
				int cursor = 0;

				public boolean hasNext() {
					return cursor < vec.length;
				}

				public int next() {
					if (!hasNext())
						throw new NoSuchElementException();
					return vec[cursor++];
				}
			};
		}

		public int containsAt(int e) {
			final int[] workArray = vec; // faster access
			for (int n = workArray.length, i = 0; i < n; i++)
				if (workArray[i] == e)
					return i;
			return -1;
		}

		public int containsAt(int e, int from) {
			final int[] workArray = vec; // faster access
			if (from < workArray.length)
				for (int n = workArray.length, i = from + 1; i < n; i++)
					if (workArray[i] == e)
						return i;
			return -1;
		}

		public int indexOf(int e) {
			final int[] workArray = vec; // faster access
			for (int i = 0, n = workArray.length; i < n; i++) {
				if (workArray[i] == e)
					return i;
			}
			return -1;
		}

		// unsupported
		public void shrink(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void shrinkTo(int arg0) {
			throw new UnsupportedOperationException();
		}

		public IVecInt pop() {
			throw new UnsupportedOperationException();
		}

		public void growTo(int arg0, int arg1) {
			throw new UnsupportedOperationException();
		}

		public void ensure(int arg0) {
			throw new UnsupportedOperationException();
		}

		public IVecInt push(int arg0) {
			throw new UnsupportedOperationException();
	 	}

		public void unsafePush(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void clear() {
			throw new UnsupportedOperationException();
		}

		public void moveTo(IVecInt arg0) {
			throw new UnsupportedOperationException();
		}

		public void moveTo2(IVecInt arg0) {
			throw new UnsupportedOperationException();
		}

		public void moveTo(int[] arg0) {
			throw new UnsupportedOperationException();
		}

		public void moveTo(int arg0, int arg1) {
			throw new UnsupportedOperationException();
		}

		public void moveTo(int i, int[] arg1) {
			throw new UnsupportedOperationException();
		}

		public void insertFirst(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void remove(int arg0) {
			throw new UnsupportedOperationException();
		}

		public int delete(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void set(int arg0, int arg1) {
			throw new UnsupportedOperationException();
		}

		public void sort() {
			throw new UnsupportedOperationException();
		}

		public void sortUnique() {
			throw new UnsupportedOperationException();
		}

		public IVecInt[] subset(int arg0) {
			throw new UnsupportedOperationException();
		}
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#clearTargets(int)
	 */	
	public boolean clearTargets() {
		clauses = clauses - numberOfTargets();
		softclauses = new HashMap<Integer, Integer>();
		return Boolean.TRUE.equals(sat);
	}

}
