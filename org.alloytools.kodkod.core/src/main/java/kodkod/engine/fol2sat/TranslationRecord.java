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
package kodkod.engine.fol2sat;

import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Variable;
import kodkod.instance.TupleSet;

/**
 * Record of a translation event.  Each translation event is described by four pieces of information:
 * <ol>
 * <li>the {@linkplain Formula formula} that was translated;</li>
 * <li>the {@linkplain Node node} from which the translated formula was derived by skolemization or through some other optimization;</li>
 * <li>the environment in which the given formula is translated, given as a binding of free variables to scalars (singleton, unary tuplesets);</li>
 * <li>the CNF literal, expressed as an integer, that represents the meaning of the given formula in the given environment.</li>
 * </ol>
 * 
 * @specfield node: Node // node that was transformed to this.translated
 * @specfield translated: Formula // the translated formula obtain from this.node
 * @specfield literal: int // cnf literal representing the meaning of this.node in this.env
 * @specfield env: Variable ->one TupleSet // bindings for free, non-skolemized variables 
 *                                         // for which this.node (or its desugared form) evaluates to this.literal   
 * @author Emina Torlak
 */
public abstract class TranslationRecord {
		
	/**
	 * Returns this.node.
	 * @return this.node.
	 */
	public abstract Node node();
	
	/**
	 * Returns this.translated.
	 * @return this.translated
	 */
	public abstract Formula translated();
	
	/**
	 * Returns this.literal.
	 * @return this.literal
	 */
	public abstract int literal();
	
	/**
	 * Returns a map view of this.env.
	 * @return this.env
	 */
	public abstract Map<Variable,TupleSet> env();
	
	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuilder ret = new StringBuilder();
		ret.append("< node: ");
		ret.append(node());
		ret.append(", literal: ");
		ret.append(literal());
		ret.append(", env: ");
		ret.append(env());
		ret.append(">");
		return ret.toString();
	}		
}