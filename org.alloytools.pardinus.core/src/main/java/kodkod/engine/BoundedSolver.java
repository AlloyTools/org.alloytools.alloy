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

import kodkod.engine.config.BoundedOptions;
import kodkod.instance.Bounds;

/**
 * An interface for bounded relational constraint solvers. These essentially
 * represent the standard {@link kodkod.engine.KodkodSolver Kodkod solvers},
 * whose interface is preserved for historical reasons. Other than requiring
 * options to specify bounded configurations, this interface does not impose
 * additional restrictions.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 *
 * @param <B>
 *            the class of bounds required by a concrete solver
 * @param <O>
 *            the class of options required by a concrete solver, which should
 *            at least consider bounded configurations
 *
 */
public interface BoundedSolver<B extends Bounds, O extends BoundedOptions>
		extends AbstractSolver<B, O> {

}
