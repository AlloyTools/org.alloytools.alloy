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
package kodkod.engine.decomp;

import kodkod.engine.Solution;
import kodkod.engine.Statistics;

/**
 * A monitor that logs and reports the progress of a decomposed model finding
 * procedure.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public interface DMonitor {

	/**
	 * Reports that a new partial solution (configuration) was found.
	 * 
	 * @param config
	 *            the new found configuration.
	 */
	public void newConfig(Solution config);

	/**
	 * The number of configurations generated in the decomposed solving process
	 * so far.
	 * 
	 * @return the number of generated configurations.
	 */
	public long getNumConfigs();

	/**
	 * The stats of the partial problem used to generate partial solutions
	 * (configurations). Only available after one configuration has been
	 * generated.
	 * 
	 * @return the statistics of the partial problem.
	 */
	public Statistics getConfigStats();

	/**
	 * The accumulated time spent generating partial solutions (configurations).
	 * The translation is counted only once.
	 * 
	 * @return the time spent generating configurations.
	 */
	public long getConfigTimes();

	/**
	 * Reports that every partial solution (configuration) has been generated.
	 * @param b 
	 */
	public void configsDone(boolean b);

	/**
	 * Whether every partial solution (configuration) has been generated (but
	 * not necessarily solved).
	 * 
	 * @return whether every configuration was generated.
	 */
	public boolean isConfigsDone();

	/**
	 * Reports that a new full solution was found.
	 * 
	 * @param sol
	 *            the new found solution.
	 */
	public void newSolution(DProblem<?> sol);

	/**
	 * Reports that a new next command was processed, and whether it was
	 * successful or timed out.
	 * 
	 * @param timeout
	 *            whether the next procedure timed out.
	 */
	public void gotNext(boolean timeout);

	/**
	 * The number of SAT solutions found so far.
	 * 
	 * @return the number of SAT solutions.
	 */
	public long getNumSATs();

	/**
	 * The number of integrated problems analyzed (i.e., that have already
	 * terminated) in the decomposed solving process so far. Not necessarily SAT.
	 * 
	 * @return the number of analyzed integrated problems.
	 */
	public long getNumRuns();

	/**
	 * The number of SAT variables solved so far.
	 * 
	 * @return the number of SAT variables.
	 */
	public long getTotalVars();

	/**
	 * The number of SAT clauses solved so far.
	 * 
	 * @return the number of SAT clauses.
	 */
	public long getTotalClauses();

	/**
	 * Reports that the amalgamated (batch) problem finished before any
	 * integrated problem.
	 */
	public void amalgamatedWon();

	/**
	 * Whether the amalgamated (batch) problem finished first.
	 * 
	 * @return whether the amalgamated problem finished first.
	 */
	public boolean isAmalgamated();

	/**
	 * Reports that the decomposed solving process terminated, and whether it
	 * was successful or timed out.
	 * 
	 * @param timeout
	 *            whether the process timed out.
	 */
	public void terminated(boolean timeout);

}