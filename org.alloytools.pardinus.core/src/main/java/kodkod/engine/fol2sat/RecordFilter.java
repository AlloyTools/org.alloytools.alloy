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
 * A filter for TranslationRecords, based on the value of a record's node and literal fields.
 **/
public interface RecordFilter {
	/**
	 * Returns true if the records with the given node,  formula derived from the node, literal, and environment
	 * should be returned by iterators produced by the {@linkplain TranslationLog#replay()} method.
	 * @return true if the records with the given node,  formula derived from the node, literal, and environment
	 * should be returned by iterators produced by {@linkplain TranslationLog#replay()}.
	 */
	public abstract boolean accept(Node node, Formula translated, int literal, Map<Variable,TupleSet> env);
	
	/**
	 * A record filter that accepts all records.
	 */
	public static RecordFilter ALL = new RecordFilter() {
		/**
		 * Returns true.
		 * @return true
		 */
		public boolean accept(Node node, Formula translated, int literal, Map<Variable,TupleSet> env) {
			return true;
		}
	};
	
}