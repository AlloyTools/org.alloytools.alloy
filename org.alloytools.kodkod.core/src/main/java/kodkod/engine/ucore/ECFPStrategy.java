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
package kodkod.engine.ucore;

import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

/**
 * A non-optimal minimization strategy based on the Empty Clause Cone algorithm.
 *
 * @author Emina Torlak
 * @see <a href=
 *      "http://research.microsoft.com/users/lintaoz/papers/SAT_2003_core.pdf">L.
 *      Zhang and S. Malik. <i>Extracting small unsatisfiable cores from
 *      unsatisfiable Boolean formula.</i> In Proceedings of Sixth International
 *      Conference on Theory and Applications of Satisfiability Testing (SAT
 *      '03). 2003.</a>
 */
public final class ECFPStrategy implements ReductionStrategy {

    private int lastCore;

    /**
     * Constructs a new instance of the empty clause cone strategy for minimizing
     * unsatisfiable cores.
     */
    public ECFPStrategy() {
        lastCore = Integer.MAX_VALUE;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.ReductionStrategy#next(kodkod.engine.satlab.ResolutionTrace)
     */
    @Override
    public IntSet next(final ResolutionTrace trace) {
        final IntSet core = trace.core();
        if (lastCore > core.size()) {
            lastCore = core.size();
            return core;
        } else {
            lastCore = Integer.MIN_VALUE;
            return Ints.EMPTY_SET;
        }
    }

}
