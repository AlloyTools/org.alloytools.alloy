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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.engine.config.PardinusOptions;
import kodkod.instance.Bounds;

/**
 * A relational constraint solver interface that support solution iteration,
 * independent of the underlying technology (bounded vs. unbounded) and
 * functionalities (temporal, target-oriented, decomposed, symbolic).
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 *
 * @param <B>
 *            the class of bounds required by a concrete solver
 * @param <O>
 *            the class of options required by a concrete solver
 */
public interface IterableSolver<B extends Bounds, O extends PardinusOptions>
		extends AbstractSolver<B, O> {

	/**
	 * Attempts to find a set of solutions to the given {@code formula} and
	 * {@code bounds} with respect to the set options or, optionally, to
	 * prove the formula's unsatisfiability. If the operation is successful, the
	 * method returns an iterator over {@link Solution} objects. If there is
	 * more than one solution, the outcome of all of them is SAT or trivially
	 * SAT. If the problem is unsatisfiable, the iterator will produce a single
	 * {@link Solution} whose outcome is UNSAT or trivially UNSAT. The set of
	 * returned solutions must be non-empty, but it is not required to be
	 * complete; a solver could simply return a singleton set containing just
	 * the first available solution.
	 */
	public Iterator<Solution> solveAll(Formula formula, B bounds);

}
