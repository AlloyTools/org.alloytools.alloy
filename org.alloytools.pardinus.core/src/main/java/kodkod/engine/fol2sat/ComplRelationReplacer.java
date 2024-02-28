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

import java.util.HashSet;
import java.util.Map;

import kodkod.ast.BinaryExpression;
import kodkod.ast.Expression;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.AbstractReplacer;

/**
 * Replaces by new relations those under difference operators in a given Node.
 * These complemented bounds, the use of lower/upper bounds will be inverted.
 * 
 * @author Nuno Macedo // [HASLab] symbolic model finding
 */
public class ComplRelationReplacer extends AbstractReplacer {
	
	private boolean neg = false;
	public final Map<Relation, Relation> compls;

	/**
	 * Constructs a new relation replacer. The given map will store the new complemented
	 * relations.
	 */
	public ComplRelationReplacer(Map<Relation,Relation> compl) {
		super(new HashSet<Node>());
		this.compls = compl;
	}
	
	/**
	 * Registers the whether the sub-trees are within a negative context.
	 * @return the expression with complemented relations replaced
	 */
	public Expression visit(BinaryExpression binExpr) {
		Expression ret = lookup(binExpr);
		if (ret!=null) return ret;
		
		final Expression left  = binExpr.left().accept(this);
		if (binExpr.op() == ExprOperator.DIFFERENCE)
			neg = !neg;
		final Expression right = binExpr.right().accept(this);
		if (binExpr.op() == ExprOperator.DIFFERENCE)
			neg = !neg;
		ret = (left==binExpr.left() && right==binExpr.right()) ?
			  binExpr : left.compose(binExpr.op(), right);
		return cache(binExpr,ret);
	}
	
	/**
	 * Replaces the relation by its complement if within a negated context.
	 * @return the new complement relation
	 */
	@Override
	public Relation visit(Relation rel) {
		Relation compl = rel;
		if (neg) {
			compl = Relation.nary(rel.name()+"_compl", rel.arity());
			compls.put(rel,compl);
		}
		return cache(rel, compl);
	}
	
}