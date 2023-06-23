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
package kodkod.engine.fol2sat;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.visitor.AbstractCollector;

/**
 * Collects relations in a given Node. 
 * 
 * @see FreeVariableCollector
 * 
 * @author Emina Torlak
 */
public class RelationCollector extends AbstractCollector<Relation> {
	
	/**
	 * Constructs a new collector using the given structural information.
	 * The given set is required to contain the syntactically shared subtrees of the
	 * node for which we are computing caching information.
	 */
	public RelationCollector(Set<Node> cached) {
		super(cached);
	}
	
	/**
	 * @see kodkod.ast.visitor.AbstractCollector#newSet()
	 */
	@Override
	protected Set<Relation> newSet() {
		return new LinkedHashSet<Relation>(2);
	}
		
	/**
	 * Returns the singleton set containing the given variable.
	 * @return {variable}
	 */
	@Override
	public Set<Relation> visit(Relation variable) {
		return cache(variable, Collections.singleton(variable));
	}
	
}