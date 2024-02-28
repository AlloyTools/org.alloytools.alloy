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
package kodkod.engine.ltl2fol;

import static kodkod.ast.operator.FormulaOperator.AND;
import static kodkod.ast.operator.FormulaOperator.OR;

import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Formula;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.RelationPredicate;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.visitor.AbstractReplacer;

/**
 * Converts an LTL temporal formula into its negated normal form (NNF), by
 * propagating negations down LTL and FOL quantifiers.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class NNFReplacer extends AbstractReplacer {

	/**
	 * Converts the given formula into the negated normal form 
	 * by pushing negations through every formula.
	 * @return the formula in negated normal form
	 */
	public static Formula nnf(Formula formula) {  
		final NNFReplacer nnf = new NNFReplacer(new HashSet<Node>(), new HashSet<Node>());
		return formula.accept(nnf);
	}
	
	/** Whether the current node is in a negated context. */
	private boolean negated = false;

	private NNFReplacer(HashSet<Node> cached, HashSet<Node> ncached) {
		super(cached);
		this.ncached = ncached;
		this.ncache = new IdentityHashMap<Node,Node>(ncached.size());
	}
	
	
	protected final Map<Node,Node> ncache;
	protected final Set<Node> ncached;

	@Override
	protected <N extends Node> N cache(N node, N replacement) {
		if (!negated) return super.cache(node,replacement);
		if (ncached.contains(node)) {
			ncache.put(node, replacement);
		}
		return replacement;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected <N extends Node> N lookup(N node) {
		if (!negated) return super.lookup(node);
		else return (N) ncache.get(node);
	}
	
	@Override
	public Formula visit(QuantifiedFormula qf) {
		Formula ret = lookup(qf);
		if (ret!=null) return ret;
		
		if (negated) {
			switch (qf.quantifier()) {
			case ALL:
				return cache(qf,qf.formula().accept(this).forSome(qf.decls()));
			case SOME:
				return cache(qf,qf.formula().accept(this).forAll(qf.decls()));
			default:
				negated = !negated;
				Formula temp = qf.accept(this);
				negated = !negated;
				return cache(qf,temp.not());
			}
		} else {
			Formula f = qf.formula().accept(this);
			return cache(qf,(QuantifiedFormula) f.quantify(qf.quantifier(), qf.decls()));
		}
	}

	@Override
	public Formula visit(NaryFormula nf) {
		Formula ret = lookup(nf);
		if (ret!=null) return ret;
		
		Formula[] arrayOfFormula = new Formula[nf.size()];
		if (negated) {
			switch (nf.op()) {
			case AND:
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = nf.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				return cache(nf,Formula.compose(OR, arrayOfFormula));
			case OR:
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = nf.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				return cache(nf,Formula.compose(AND, arrayOfFormula));
			default:
				negated = !negated;
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = nf.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				negated = !negated;
				return cache(nf,Formula.compose(nf.op(), arrayOfFormula).not());
			}
		} else {
			for (int j = 0; j < arrayOfFormula.length; j++) {
				Formula localFormula2 = nf.child(j);
				arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
			}
			return cache(nf,Formula.compose(nf.op(), arrayOfFormula));
		}

	}

	@Override
	public Formula visit(BinaryFormula bf) {
		Formula ret = lookup(bf);
		if (ret!=null) return ret;
		
		Formula left_t, right_t, left_f, right_f;
		if (negated) {
			switch (bf.op()) {
			case IMPLIES: // !(a => b) = !(!a || b) = a && !b
				right_f = bf.right().accept(this);
				negated = !negated;
				left_t = bf.left().accept(this);
				negated = !negated;
				return cache(bf,left_t.and(right_f));
			case IFF: // !(a <=> b) = !( (a | !b) & (!a | b)) = !(a | !b) | !(!
						// a | b) = (!a & b) | (a & !b)
				negated = !negated;
				left_t = bf.left().accept(this);
				right_t = bf.right().accept(this);
				negated = !negated;
				left_f = bf.left().accept(this);
				right_f = bf.right().accept(this);
				return cache(bf,(left_f.and(right_t)).or(left_t.and(right_f)));
			case AND:
				left_f = bf.left().accept(this);
				right_f = bf.right().accept(this);
				return cache(bf,left_f.or(right_f));
			case OR:
				left_f = bf.left().accept(this);
				right_f = bf.right().accept(this);
				return cache(bf,left_f.and(right_f));
			default:
				negated = !negated;
				left_t = bf.left().accept(this);
				right_t = bf.right().accept(this);
				negated = !negated;
				return cache(bf,left_t.compose(bf.op(), right_t).not());
			}
		} else {
			switch (bf.op()) {
			case IMPLIES: // (a => b) = (!a || b)
				right_t = bf.right().accept(this);
				negated = !negated;
				left_f = bf.left().accept(this);
				negated = !negated;
				return cache(bf,left_f.or(right_t));
			case IFF: // (a <=> b) = ((a | !b) & (!a | b))
				left_t = bf.left().accept(this);
				right_t = bf.right().accept(this);
				negated = !negated;
				left_f = bf.left().accept(this);
				right_f = bf.right().accept(this);
				negated = !negated;
				return cache(bf,(left_t.or(right_f)).and(left_f.or(right_t)));
			default:
				left_t = bf.left().accept(this);
				right_t = bf.right().accept(this);
				return cache(bf,left_t.compose(bf.op(), right_t));
			}
		}

	}

	@Override
	public Formula visit(NotFormula nf) {
		Formula ret = lookup(nf);
		if (ret!=null) return ret;
		
		negated = !negated;
		Formula temp = nf.formula().accept(this);
		negated = !negated;
		return cache(nf,temp);
	}

	@Override
	public Formula visit(UnaryTempFormula tf) {
		Formula ret = lookup(tf);
		if (ret!=null) return ret;
		
		if (negated) {
			switch (tf.op()) {
			case ALWAYS:
				return cache(tf,tf.formula().accept(this).eventually());
			case EVENTUALLY:
				return cache(tf,tf.formula().accept(this).always());
			case HISTORICALLY:
				return cache(tf,tf.formula().accept(this).once());
			case ONCE:
				return cache(tf,tf.formula().accept(this).historically());
			case AFTER:
				return cache(tf,tf.formula().accept(this).after());
			case BEFORE:
				return cache(tf,tf.formula().accept(this).before());
			default:
				negated = !negated;
				Formula temp = tf.formula().accept(this);
				negated = !negated;
				return cache(tf,temp.apply(tf.op()).not());
			}
		} else {
			Formula f = tf.formula().accept(this);
			return cache(tf,f.apply(tf.op()));
		}
	}

	@Override
	public Formula visit(BinaryTempFormula tf) {
		Formula ret = lookup(tf);
		if (ret!=null) return ret;
		
		if (negated) {
			switch (tf.op()) {
			case UNTIL: case RELEASES: case SINCE: case TRIGGERED:
				return cache(tf,tf.left().accept(this).compose(tf.op(),tf.right().accept(this)));
			default:
				negated = !negated;
				Formula temp1 = tf.left().accept(this);
				Formula temp2 = tf.right().accept(this);
				negated = !negated;
				return cache(tf,temp1.compose(tf.op(), temp2).not());
			}
		} else {
			Formula left = tf.left().accept(this);
			Formula right = tf.right().accept(this);
			return cache(tf,left.compose(tf.op(), right));
		}
	}
	
	@Override
	public Formula visit(ConstantFormula cf) { 
		Formula ret = lookup(cf);
		if (ret!=null) return ret;

		Formula res;
		if (negated && cf.equals(Formula.FALSE))
			res = Formula.TRUE;
		else if (negated && cf.equals(Formula.TRUE))
			res = Formula.FALSE;
		else res = cf;
		
		return visitFormula(res); 
	}

	final Formula visitFormula(Formula f) { 
		Formula ret = lookup(f);
		if (ret!=null) return ret;
		
		return negated? cache(f,f.not()) : cache(f,f); 
		
	}
	
	@Override
	public Formula visit(ComparisonFormula cf) 		{ return visitFormula(cf); }

	@Override
	public Formula visit(MultiplicityFormula mf) 	{ return visitFormula(mf); }

	@Override
	public Formula visit(RelationPredicate rp) 		{ return visitFormula(rp); }
	
	@Override
	public Formula visit(IntComparisonFormula icf) 	{ return visitFormula(icf); }


}
