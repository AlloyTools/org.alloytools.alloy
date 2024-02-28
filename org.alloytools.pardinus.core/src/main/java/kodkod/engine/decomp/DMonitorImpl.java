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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.engine.config.Reporter;

/**
 * An implementation of a monitor that logs and reports the progress of a
 * decomposed model finding procedure using a regular Kodkod reporter.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class DMonitorImpl implements DMonitor {

	private final Reporter rep;

	private int configs = 0;
	private long config_times = -1;
	private Statistics config_stats = null;
	private boolean configs_done = false;

	private long sats = 0;
	private long vars = 0;
	private long clauses = 0;
	private final List<DProblem<?>> solutions = new ArrayList<DProblem<?>>();
	private boolean amalgamated_won = false;

	/**
	 * Constructs a new decomposed solving monitor that reports through a Kodkod
	 * reporter.
	 * 
	 * @param rep
	 *            the reporter.
	 */
	public DMonitorImpl(Reporter rep) {
		this.rep = rep;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public synchronized void newConfig(Solution config) {
		// first config, get stats and translation time
		if (config_times < 0) {
			config_stats = config.stats();
			config_times = config.stats().translationTime();
		}
		config_times += config.stats().solvingTime();
		if (config.sat()) {
			configs++;
			rep.debug("Config: " + configs + " " + config.outcome().toString()
					+ "; " + config.instance().relationTuples().toString());
		}
		else 
			rep.debug("Config: " + configs + " " + config.outcome().toString());
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Statistics getConfigStats() {
		return config_stats;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getConfigTimes() {
		return config_times;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean isConfigsDone() {
		return configs_done;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getNumConfigs() {
		return configs;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void configsDone(boolean next) {
		rep.reportConfigs(configs, config_stats.primaryVariables(), config_stats.variables(), config_stats.clauses());
		if (!next) {
			rep.debug("Config: " + "Done");
			configs_done = true;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public synchronized void newSolution(DProblem<?> sol) {
		Entry<Solution, Iterator<Solution>> se = sol.getSolutions();
		if (se.getKey().sat()) {
			sats++;
			rep.debug("Solution: " + sats + " " + se.getKey().outcome());
		} else {
			rep.debug("Solution: " + se.getKey().outcome());
		}
		vars += se.getKey().stats().primaryVariables();
		clauses += se.getKey().stats().clauses();
		solutions.add(sol);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getNumSATs() {
		return sats;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getNumRuns() {
		return solutions.size();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTotalVars() {
		return vars;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTotalClauses() {
		return clauses;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void gotNext(boolean timeout) {
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void amalgamatedWon() {
		rep.debug("Amalgamated: " + "Done");
		amalgamated_won = true;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean isAmalgamated() {
		return amalgamated_won;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void terminated(boolean timeout) {
		rep.debug("Solving: " + "Done");
	}

}
