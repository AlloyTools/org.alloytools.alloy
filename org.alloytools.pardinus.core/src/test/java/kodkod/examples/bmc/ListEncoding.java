/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.examples.bmc;

import java.util.ArrayList;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Encoding skeleton; some parts will change depending on whether 
 * we are performing verification, repair or synthesis.
 * 
 * @author Emina Torlak
 *
 */
abstract class ListEncoding {
	final Relation list, node, string, thisList, nil, head, next, data; 

	ListEncoding() {
		list = Relation.unary("List");
		node = Relation.unary("Node");
		string = Relation.unary("String");
		thisList = Relation.unary("this");
		nil = Relation.unary("null");
		head = Relation.binary("head");
		next = Relation.binary("next");
		data  = Relation.binary("data");
	}
	
	private Formula invariants(Expression thisList, Expression next, Expression data, Expression head) {
		return Formula.and(
			thisList.in(list), 																// this in List
			thisList.one(),																	// one this
			function(next, node, node.union(nil)),											// next in Node ->one Node + nil
			acyclic(next),																	// no iden & ^next
			function(data, node, string.union(nil)),										// data in Node ->one String + nil
			function(head, list, node.union(nil)));											// head in List ->one Node + nil
	}
	
	Formula pre() { 	
		final Expression thisHead = thisList.join(head);
		return Formula.and(	invariants(thisList, next, data, head), 						// assume invariants(this, next, data, head) &&
							thisHead.eq(nil).not(), 										//   this.head != null && 
							thisHead.join(next).eq(nil).not());			   					//   this.head.next != null
	}

	Expression nearNode0() { return thisList.join(head); }									// nearNode0 := this.head
	Expression midNode0()  { return nearNode0().join(next); }								// midNode0 := nearNode0.next
	Expression farNode0()  { return midNode0().join(next); }								// farNode0 := midNode0.next
	
	Expression next0()     { return next.override(nearNode0().product(farNode0())); }		// next0 := update(next, nearNode0 -> farNode0)
																							// [fix] next0 := update(next, nearNode0 -> nil) 
	Formula guard0()       { return farNode0().eq(nil).not(); }								// guard0 := farNode0 != null
	Expression next1()     { return next0().override(midNode0().product(nearNode0())); }	// next1 := update(next0, midNode0 -> nearNode0)
	Expression nearNode1() { return midNode0(); }											// nearNode1 := midNode0
	Expression midNode1()  { return farNode0(); }											// midNode1 := farNode0
	Expression farNode1()  { return farNode0().join(next1()); }								// farNode1 := farNode0.next1
	
	Expression next2()     { return guard0().thenElse(next1(), next0()); }					// next2 := phi(guard0, next1, next0)
	Expression nearNode2() { return guard0().thenElse(nearNode1(), nearNode0()); } 			// nearNode2 := phi(guard0, nearNode1, nearNode0)
	Expression midNode2()  { return guard0().thenElse(midNode1(), midNode0()); }			// midNode2 := phi(guard0, midNode1, midNode0)
	Expression farNode2()  { return guard0().thenElse(farNode1(), farNode0()); }			// farNode2 := phi(guard0, farNode1, farNode0)
	
	Formula loopGuard()    { return farNode2().eq(nil); }									// assume farNode2 = null
		 							
	Expression next3()     { return next2().override(midNode2().product(nearNode2())); }	// next3 = update(next2, midNode2 -> nearNode2)
	Expression head0()     { return head.override(thisList.product(midNode2())); }			// head0 = update(head, this -> midNode2)
	
	Formula post() { 				
		Expression nodes = thisList.join(head).join(next.reflexiveClosure());				// assert let nodes = this.head.*next, 
		Expression nodesPrime = thisList.join(head0()).join(next3().reflexiveClosure());	//   nodes' = this.head0.*next3, 
		Expression ns = nodes.difference(nil);												//   ns = nodes - nil | 
		Expression ns2 = ns.product(ns);
		return Formula.and(	invariants(thisList, next3(), data, head0()),					//   invariants(this, next3, data, head0) &&  
							nodesPrime.eq(nodes),											//   nodes' = nodes &&
							next3().intersection(ns2).										//   next3 & (ns -> ns) = ~(next & (ns -> ns))
								eq(next.intersection(ns2).transpose())); 
	}
	 
	/*----------------- bounds construction -----------------*/
	Bounds bounds(int size) {			 
		
		final Universe u = universe(size);
		final Bounds b = new Bounds(u);
		final TupleFactory t = u.factory();
		final int max = size-1;
		
		b.bound(list, t.setOf("l0"));
		b.bound(node, t.range(t.tuple("n0"), t.tuple("n" + max)));
		b.bound(string, t.range(t.tuple("s0"), t.tuple("s" + max)));
		b.bound(thisList, b.upperBound(list));
		b.boundExactly(nil, t.setOf("nil"));
		
		TupleSet ran = t.range(t.tuple("n0"), t.tuple("n" + max)); 
		ran.add(t.tuple("nil"));
		b.bound(head, b.upperBound(list).product(ran));
		
		ran = t.range(t.tuple("n0"), t.tuple("n" + max)); 
		ran.add(t.tuple("nil"));
		b.bound(next, b.upperBound(node).product(ran));
		
		ran = t.range(t.tuple("s0"), t.tuple("s" + max)); 
		ran.add(t.tuple("nil"));
		b.bound(data, b.upperBound(node).product(ran));
		
		return b;
	}
	
	Universe universe(int size) {
		final ArrayList<Object> elts = new ArrayList<Object>(2 + size * 2);
		elts.add("l0");
		for(int i = 0; i < size; i++) { elts.add("n" + i); }
		for(int i = 0; i < size; i++) { elts.add("s" + i); }
		elts.add("nil");
		return new Universe(elts);
	}
	
	/*----------------- helpers -----------------*/
	
	/**
     * Returns a formula stating that the given expression is acyclic.
     * @return {f: Formula | f <=> no ^expr & iden}
     * @throws IllegalArgumentException  expr.arity != 2
     */
    public Formula acyclic(Expression expr) {
    	if (expr instanceof Relation)
    		return ((Relation)expr).acyclic();  // special handling for relations that enables better symmetry breaking
    	
    	if (expr.arity() != 2) throw new IllegalArgumentException();
    	return expr.closure().intersection(Expression.IDEN).no();
    }
    
    /**
     * Returns a formula stating that the given relation is a total function
     * with the specified domain and range.
     * @return {f: Formula | f <=> expr in domain->range && all v: domain | one v.expr }
     * @throws NullPointerException  domain = null || range = null
     * @throws IllegalArgumentException  domain.arity != 1 || range.arity != 1
     * @throws IllegalArgumentException  this.arity != 2
     */
    public Formula function(Expression expr, Expression domain, Expression range) {
    	if (expr instanceof Relation)
    		return ((Relation)expr).function(domain, range);  // special handling for relations that enables better symmetry breaking
    	
    	if (domain.arity() != 1 || range.arity() != 1)
			throw new IllegalArgumentException("invalid arity: " + domain + " or " + range);
		// expr in domain->range 
		final Formula domainConstraint = expr.in(domain.product(range));
		// all v: domain | one v.expr
		final Variable v = Variable.unary("v"+expr.hashCode());
		final Formula funConstraint = v.join(expr).one().forAll(v.oneOf(domain));
		// expr in domain->range && all v: domain | targetMult v.relation
		return domainConstraint.and(funConstraint);
    }
    
    TupleSet copyFrom(TupleFactory tf, TupleSet other) {
    	final int arity = other.arity();
    	final TupleSet out = tf.noneOf(arity);
    	final Object[] tmp = new Object[arity];
    	for(Tuple t : other) { 
    		for(int i = 0; i < arity; i++) {
    			tmp[i] = t.atom(i);
    		}
    		out.add(tf.tuple((Object[])tmp));
    	}
    	return out;
    }
}
