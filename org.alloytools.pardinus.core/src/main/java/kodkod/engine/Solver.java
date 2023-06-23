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
package kodkod.engine;

import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATProver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

/** 
 * A computational engine for solving relational satisfiability problems. 
 * Such a problem is described by a {@link kodkod.ast.Formula formula} in 
 * first order relational logic; finite {@link kodkod.instance.Bounds bounds} on 
 * the value of each {@link Relation relation} constrained by the formula; and 
 * a set of {@link kodkod.engine.config.Options options} specifying, among other global 
 * parameters, the length of bitvectors that describe the meaning of 
 * {@link IntExpression integer expressions} in the given formula.  The options are 
 * usually reused between invocations to the {@linkplain #solve(Formula, Bounds) solve}
 * methods, so they are specified as a part of the {@linkplain KodkodSolver solver} state. 
 *
 * <p>
 * A {@link Solver} takes as input a relational problem and produces a 
 * satisfying model or an {@link Instance instance} of it, if one exists.  It can also 
 * produce a {@link Proof proof} of unsatisfiability for problems with no models, 
 * if the {@link kodkod.engine.config.Options options} specify the use of a 
 * {@linkplain SATProver proof logging SAT solver}.
 * </p> 
 * 
 * @specfield options: Options 
 * @author Emina Torlak 
 * @modified Nuno Macedo // [HASLab] model finding hierarchy
 */
// [HASLab] solver hierarchy
public final class Solver extends AbstractKodkodSolver<Bounds,Options> { 

	private Options options;

	/**
	 * Returns the Options object used by this Solver
	 * to guide translation of formulas from first-order
	 * logic to cnf.
	 * @return this.options
	 */
	public Options options() {
		return options;
	}
	
	/**
	 * Constructs a new Solver with the default options.
	 * @ensures this.options' = new Options()
	 */
	public Solver() {
		this.options = new Options();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * @ensures this.options' = options
	 * @throws NullPointerException  options = null
	 */
	public Solver(Options options) {
		if (options == null)
			throw new NullPointerException();
		this.options = options;
	}
}
