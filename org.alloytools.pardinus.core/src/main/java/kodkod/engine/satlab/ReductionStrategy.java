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

import kodkod.util.ints.IntSet;


/**
 * Strategy for reducing the unsatisfiable core of
 * a {@link SATProver}.  
 * @specfield traces: ResolutionTrace[]
 * @specfield nexts: IntSet[]
 * @invariant #traces = #nexts
 * @invariant no disj i,j: [0..#nexts) | traces[i] = traces[j] && nexts[i] = nexts[j]
 * @see SATProver#reduce(ReductionStrategy)  
 * @author Emina Torlak
 */
public interface ReductionStrategy {

	/**
	 * Returns the next subtrace of the specified trace to be analyzed, given 
	 * as a set of indices into the trace.   
	 * If there are no more subtraces to be analyzed (i.e. the given trace is 
	 * minimal according to the minimality measure used by this strategy),
	 * returns the empty set.
	 * @requires 
	 * <pre>
	 * let t = this.traces[#this.traces-1], n = this.nexts[#this.nexts-1] | 
	 *  unsat(t.elts[n].literals) => 
	 *   (all i: n.ints | let j = #{k: n.ints | k < i} | t.elts[i].equals(trace.elts[j])) 
	 *  else
	 *   trace = t
	 * </pre>
	 * @ensures 
	 * <pre> 
	 *  let next = { i: int | 0 <= i < trace.size()-1 } |
	 *   trace.elts[next].antecedents in trace.elts[next] and 
	 *   (some i: [0..#trace) | i !in next and no trace[i].antecedents) and  
	 *   this.nexts' = this.nexts + #this.nexts->next and
	 *   this.traces' = this.traces + #this.traces->trace 
	 * </pre>
	 * @return this.nexts'[#this.nexts-1]
	 */
	public IntSet next(ResolutionTrace trace);
	
}
