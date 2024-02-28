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

import kodkod.ast.Formula;
import kodkod.engine.config.PardinusOptions;
import kodkod.engine.satlab.SATProver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

/**
 * The most general relational constraint solver interface, independent of the
 * underlying technology (bounded vs. unbounded) and functionalities (temporal,
 * target-oriented, decomposed, symbolic). This may require different
 * instantiations of bounds and model finding options.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 *
 * @param <B>
 *            the class of bounds required by a concrete solver
 * @param <O>
 *            the class of options required by a concrete solver
 */
public interface AbstractSolver<B extends Bounds, O extends PardinusOptions> {

	/**
	 * Returns the options object used by this solver to guide translation and
	 * solving of model finding problems.
	 * 
	 * @return the options
	 */
	public O options();

	/**
	 * Attempts to satisfy the given {@code formula} and {@code bounds} with
	 * respect to set options or, optionally, prove the problem's
	 * unsatisfiability. If the method completes normally, the result is a
	 * {@linkplain Solution solution} containing either an {@linkplain Instance
	 * instance} of the given problem or, optionally, a {@linkplain Proof proof}
	 * of its unsatisfiability. An unsatisfiability proof will be constructed
	 * iff the options specify a {@linkplain SATProver} and
	 * {@code this.options.logTranslation > 0}.
	 */
	public Solution solve(Formula formula, B bounds);

	/**
	 * Releases the resources, if any, associated with this solver.
	 */
	public void free();

}
