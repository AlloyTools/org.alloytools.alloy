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
package kodkod.engine;

import kodkod.engine.fol2sat.Translation;

/**
 * Stores the statistics gathered while solving
 * a given formula.
 * @specfield formula: Formula // the formula being solved
 * @specfield bounds: Bounds // the bounds on the formula
 * 
 * @modified Nuno Macedo // [HASLab] temporal model finding
 */
public final class Statistics {
	
	private static final String NEW_LINE = System.getProperty("line.separator");
	
	// [HASLab] remove final
	private int vars, pVars, clauses;
	private long translation, solving; 
	
	/**
	 * Constructs a new Statistics object using the provided values.
	 */
	Statistics(int primaryVariables, int variables, int clauses, 
			   long translationTime, long solvingTime) {
		this.pVars = primaryVariables;
		this.vars = variables;
		this.clauses = clauses;
		this.translation = translationTime;
		this.solving = solvingTime;
	}
	
	/**
	 * Constructs a new Statistics object using the provided values.
	 */
	Statistics(Translation translation, long translationTime, long solvingTime) { 
		this(translation.numPrimaryVariables(), translation.cnf().numberOfVariables(), 
				translation.cnf().numberOfClauses(), translationTime, solvingTime);
	}
	
	// [HASLab]
	public void update(Translation translation, long translationTime, long solvingTime) {
		this.pVars += translation.numPrimaryVariables();
		this.vars += translation.cnf().numberOfVariables();
		this.clauses += translation.cnf().numberOfClauses();
		this.translation += translationTime;
		this.solving += solvingTime;
	}
	
	/**
	 * Returns the number of variables needed 
	 * to encode this.formula in CNF.
	 * @return the number of variables needed
	 * to encode this.formula in CNF.
	 */
	public int variables() {
		return vars;
	}
	
	/**
	 * Returns the number of primary variables
	 * used in the encoding of this.formula; i.e. the variables
	 * allocated to all the relations at the leaves
	 * of this.formula.
	 * @return the number of primary variables
	 * used in the encoding of this.formula
	 */
	public int primaryVariables() {
		return pVars;
	}
	
	/**
	 * Returns the number of clauses needed to 
	 * encode this.formula in CNF.
	 * @return the number of variables needed
	 * to encode this.formula in CNF.
	 */
	public int clauses() {
		return clauses;
	}
	
	/**
	 * Returns the number of miliseconds spent
	 * on translation this.formula to CNF.
	 * @return the number of miliseconds spent
	 * on translation this.formula to CNF.
	 */
	public long translationTime() {
		return translation;
	}
	
	/**
	 * Returns the number of miliseconds spent
	 * on solving the CNF encoding of this.formula.
	 * @return the number of miliseconds spent
	 * on solving the CNF encoding of this.formula.
	 */
	public long solvingTime() {
		return solving;
	}
	
	/**
	 * Returns a string representation of this
	 * Statistics object.
	 * @return a string representation of this
	 * Statistics object.
	 */
	public String toString() {
		final StringBuilder ret = new StringBuilder();
		ret.append("p cnf ");
		ret.append(vars);
		ret.append(" ");
		ret.append(clauses);
		ret.append(NEW_LINE);
		ret.append("primary variables: ");
		ret.append(pVars);
		ret.append(NEW_LINE);
		ret.append("translation time: ");
		ret.append(translation);
		ret.append(" ms").append(NEW_LINE);
		ret.append("solving time: ");
		ret.append(solving);
		ret.append(" ms");
		return ret.toString();
	}
}