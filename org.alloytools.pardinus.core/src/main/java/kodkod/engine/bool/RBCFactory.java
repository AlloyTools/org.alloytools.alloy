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
package kodkod.engine.bool;

import static kodkod.engine.bool.BooleanConstant.FALSE;
import static kodkod.engine.bool.BooleanConstant.TRUE;
import static kodkod.engine.bool.Operator.AND;
import static kodkod.engine.bool.Operator.CONST;
import static kodkod.engine.bool.Operator.ITE;
import static kodkod.engine.bool.Operator.OR;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import kodkod.util.collections.CacheSet;

/**
 * A factory for creating variables, binary gates, and if-then-else gates, in RBC form.
 * @specfield values: set (BooleanVariable + MultiGate + ITEGate)
 * @specfield cmpMax: int // the maximum number of comparisons made when comparing circuits for equality
 * @invariant no disj factory, factory' : CircuitFactory | some factory.values & factory'.values
 * @author Emina Torlak
 */
final class RBCFactory {
	/**
	 * Stores input variables.
	 * @invariant all i: [1..iLits.size()] | vars[i-1].positive.label = i
	 */
	private final BooleanVariable[] vars;
	/**
	 * Caches the AND, OR, and ITE gates.  
	 * @invariant all i: [0..2] | c[i].op.ordinal = i
	 */
	private final CacheSet<BooleanFormula>[] cache;
	private int label, cmpMax;
	
	
	/**
	 * Constructs a CircuitFactory using the given max comparison parameter, initialized
	 * to contain the given number of variables. 
	 * @requires cmpMax > 0 && numVars >= 0
	 * @ensures #this.values' = numVars && this.values in BooleanVariable
	 * @ensures this.cmpMax' = cmpMax
	 */
	@SuppressWarnings("unchecked") RBCFactory(int numVars, int cmpMax) {
		assert cmpMax > 0 && numVars >= 0;
		this.cmpMax = cmpMax;
		this.label = numVars + 1;
		vars = new BooleanVariable[numVars];
		for(int i = 0; i < numVars; i++) {
			vars[i]= new BooleanVariable(i+1);                                                                        
		}

		cache = new CacheSet[]{new CacheSet<BooleanFormula>(), new CacheSet<BooleanFormula>(), new CacheSet<BooleanFormula>()};
	}
	
	/**
	 * Returns the cache for gates with the given operator.
	 * @requires op in AND + OR + ITE
	 * @return cache[op.ordinal]
	 */
	private CacheSet<BooleanFormula> opCache(Operator op) {
		return cache[op.ordinal];
	}
	
	/**
	 * Sets this.cmpMax to the given value.
	 * @requires cmpMax > 0
	 * @ensures this.cmpMax' = cmpMax
	 */
	void setCmpMax(int cmpMax) {
		assert cmpMax > 0;
		this.cmpMax = cmpMax;
	}
	
	/**
	 * Returns this.cmpMax.
	 * @return this.cmpMax
	 */
	int cmpMax() { return cmpMax; }
	
	/**
	 * Removes all MultiGates and ITEGates from this.factory.
	 * @ensures this.values' = this.values & BooleanVariable 
	 */
	void clear() {
		label = vars.length+1;
		cache[0].clear();
		cache[1].clear();
		cache[2].clear();
	}
	
	/**
	 * Returns true if the given value
	 * is a valid argument to one of the <tt>assemble</tt>
	 * methods.  Otherwise returns false.
	 * @return v in this.values + this.values.negation + BooleanConstant
	 */
	boolean canAssemble(BooleanValue v) {
		if (v.op()==CONST) return true;
		if (v.label() < 0) v = v.negation();
		final int absLit = v.label();
		if (absLit <= vars.length) {
			return v == vars[absLit-1];
		} else {
			final BooleanFormula g = (BooleanFormula) v;
			for(Iterator<BooleanFormula> gates = opCache(g.op()).get(g.hashCode()); gates.hasNext(); ) {
			    	if (gates.next()==g) return true;
		    }
			return false;
		}
	}
	
	/**
	 * Returns the number of variables in this factory.
	 * @return #(this.values & BooleanVariable)
	 */
	int numVars() { return vars.length; }
	
	/**
	 * Returns the boolean variable from this.values with the given label.
	 * @requires 0 < label <= #(this.values & BooleanVariable)
	 * @return (this.values & BooleanVariable).label 
	 */
	BooleanVariable variable(int label) {
		return vars[label-1];
	}
	
	/**
	 * Returns a boolean value whose meaning is (if [[i]] then [[t]] else [[e]]).
	 * @requires i + t + e in (this.values + this.values.negation + BooleanConstant)
	 * @return v: BooleanValue | [[v]] = if [[i]] then [[t]] else [[e]] 
	 * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v, this.values' = this.values
	 * @throws NullPointerException  any of the arguments are null
	 */
	BooleanValue assemble(BooleanValue i, BooleanValue t, BooleanValue e) {
		if (i==TRUE || t==e) return t;
		else if (i==FALSE) return e;
		else if (t==TRUE || i==t) return assemble(OR, i, e);
		else if (t==FALSE || i.negation()==t) return assemble(AND, i.negation(), e);
		else if (e==TRUE || i.negation()==e) return assemble(OR, i.negation(), t);
		else if (e==FALSE || i==e) return assemble(AND, i, t);
		else {
			final int ilabel = i.label(), tlabel = t.label(), elabel = e.label();
			boolean neg = false;
			BooleanFormula f0 = (BooleanFormula) i, f1 = (BooleanFormula) t, f2 = (BooleanFormula) e;
			if (Math.abs(tlabel)==Math.abs(elabel)) { 
				if (ilabel>0 && tlabel<0 && elabel>0) { // (a <=> !b) becomes !(a <=> b)
					neg = true;
					f1 = f1.negation();
					f2 = f2.negation();
				} else if (ilabel<0 && tlabel>0 && elabel<0) { // (!a <=> b) becomes !(a <=> b)
					neg = true;
					f0 = f0.negation(); 
				} else if (ilabel<0 && tlabel<0 && elabel>0) {// (!a <=> !b) becomes (a <=> b)
					f0 = f0.negation();
					f1 = f1.negation();
					f2 = f2.negation();
				}
			} 
			
			final int hash = ITE.hash(f0, f1, f2);
			
			for(Iterator<BooleanFormula> gates = opCache(ITE).get(hash); gates.hasNext();) {
				BooleanFormula gate = gates.next();
				if (gate.input(0)==i && gate.input(1)==t && gate.input(2)==e)
					return gate;
			}
			final BooleanFormula ret = new ITEGate(label++, hash, f0, f1, f2);
			opCache(ITE).add(ret);
			return neg ? ret.negation() : ret;
		}
	}
	
	/**
	 * Returns a boolean value whose meaning is ([[v0]] op [[v1]]).
	 * @requires v0 + v1 in (this.values + this.values.negation + BooleanConstant)
	 * @return  v: BooleanValue | [[v]] = [[v0]] op [[v1]] 
	 * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v, this.values' = this.values
	 * @throws NullPointerException  any of the arguments are null
	 */
	BooleanValue assemble(Operator.Nary op, BooleanValue v0, BooleanValue v1) {
		if (op==OR) {
			return assemble(AND, v0.negation(), v1.negation()).negation();
		}
		
		if (v0==v1) return v0;
		if (v0.label()==-v1.label()) return FALSE;
		if (v0==TRUE) return v1;
		if (v1==TRUE) return v0;
		if (v0==FALSE) return FALSE;
		if (v1==FALSE) return FALSE;
		
		return cache(op, (BooleanFormula)v0, (BooleanFormula)v1);
	}
	
	/**
	 * Returns a boolean value with the same meaning as the given accumulator.
	 * @requires acc.components in (this.values + this.values.negation + BooleanConstant)
	 * @return v: BooleanValue | [[v]] = [[acc]] 
	 * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v, this.values' = this.values
	 * @throws NullPointerException  any of the arguments are null
	 */
	BooleanValue assemble(BooleanAccumulator acc) {
		final int asize = acc.size();
		final Operator.Nary op = acc.op;
		switch(asize) {
		case 0 : return op.identity();
		case 1 : return acc.iterator().next();
		case 2 : 
			final Iterator<BooleanValue> inputs = acc.iterator();
			return assemble(op, inputs.next(), inputs.next());
		default :
			final List<BooleanValue> vals = new LinkedList<BooleanValue>();
			for(BooleanValue v : acc) { 
				vals.add(v);
			}
			while(vals.size()>1) { 
				final ListIterator<BooleanValue> itr = vals.listIterator();
				for(int i = 0, max = vals.size()-1; i < max; i+=2) { 
					final BooleanValue v0 = itr.next();
					itr.remove();
					final BooleanValue v1 = itr.next();
					final BooleanValue v0opv1 = assemble(op, v0, v1);
					if (v0opv1==op.shortCircuit()) return op.shortCircuit();
					else if (v0opv1==op.identity()) itr.remove();
					else itr.set(v0opv1);
				}
			}
			return vals.get(0);
		}
	}
	
	/**
	 * Returns a BooleanFormula f such that [[f]] = f0 op f1.  The method
	 * requires that the formulas f0 and f1 be already reduced with respect to op.
	 * A new formula is created and cached iff the circuit with the meaning
	 * [[f0]] op [[f1]] has not already been created.
	 * @requires f0 and f1 have already been reduced with respect to op; i.e.  
	 * f0 op f1 cannot be reduced to a constant or a simple circuit 
	 * by applying absorption, idempotence, etc. laws to f0 and f1.
	 * @return f : BooleanFormula | [[f]] = [[f0]] op [[f1]]
	 * @ensures f !in this.values => this.values' = this.values + f,
	 * 	        this.values' = this.values
	 */
	private BooleanFormula cache(Operator.Nary op, BooleanFormula f0, BooleanFormula f1) {
		final BooleanFormula l, h;
		if (f0.label()<f1.label()) {
			l = f0; h = f1;
		} else {
			l = f1; h = f0;
		}
		final int hash = op.hash(l,h);
		for(Iterator<BooleanFormula> gates = opCache(op).get(hash); gates.hasNext(); ) {
			BooleanFormula gate = gates.next();
			if (gate.size()==2 && gate.input(0)==l && gate.input(1)==h)
				return gate;
		}
		final BooleanFormula ret = new BinaryGate(op, label++, hash, l, h);
		opCache(op).add(ret);
		return ret;
	}
	
	
}
