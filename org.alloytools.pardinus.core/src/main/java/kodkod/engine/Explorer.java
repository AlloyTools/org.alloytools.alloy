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
import java.util.Set;

import kodkod.ast.Relation;

/**
 * An iterator implementing more advanced iteration strategies for temporal
 * solutions.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding, temporal scenario
 *         exploration
 *
 * @param <T> The type to be iterated.
 */
public interface Explorer<T> extends Iterator<T> {

	/**
	 * Produces an alternative solution by iterating over the static relations,
	 * i.e., the configuration, while leaving the mutable ones free to adapt.
	 * 
	 * @return the next branching solution
	 */
	public T nextC();

	/**
	 * Produces an alternative solution by iterating over the mutable relations
	 * while fixing the static ones, i.e., the configuration.
	 * 
	 * @return the next branching solution
	 */
	public T nextP();

	/**
	 * Produces an alternative solution by iterating over the selected {@code state}
	 * of the trace, fixing all previous states. A set {@code change} of relations
	 * can be specified on which a change must occur.
	 * 
	 * @param state  the state which will be iterated.
	 * @param delta  the number of states from <state>, inclusive, in which the
	 *               change must occur
	 * @param change a set of relations in which the change must occur
	 * @return the next branching solution
	 */
	public T nextS(int state, int delta, Set<Relation> change);

	/**
	 * Whether there is a next configuration.
	 * 
	 * @return true if another configuration
	 */
	public boolean hasNextC();

	/**
	 * Whether there is a next path for the current configuration. Is reseted by a
	 * new configuration.
	 * 
	 * @return true if another path for this configuration
	 */
	public boolean hasNextP();

}
