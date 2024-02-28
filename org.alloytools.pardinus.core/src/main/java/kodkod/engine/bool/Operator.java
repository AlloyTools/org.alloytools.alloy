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

import java.util.Iterator;

/**
 * ExprOperator associated with a {@link kodkod.engine.bool.BooleanValue boolean value}.
 * 
 * @specfield ordinal: [0..5]
 * @invariant AND.ordinal = 0 && OR.ordinal = 1 && ITE.ordinal = 2 &&
 * NOT.ordinal = 2 && VAR.ordinal = 4  && CONST.ordinal = 5
 * @author Emina Torlak
 */
public abstract class Operator implements Comparable<Operator>{
	final int ordinal;
	
	private Operator(int ordinal) {	
		this.ordinal = ordinal;
	}

	/**
	 * Returns the ordinal of this operator constant.
	 * @return the ordinal of this operator constant.
	 */
	public final int ordinal() {
		return ordinal;
	}
	
	/**
	 * Returns an integer i such that i < 0 if this.ordinal < op.ordinal,
	 * i = 0 when this.ordinal = op.ordinal, and i > 0 when this.ordinal > op.ordinal.
	 * @return i: int | this.ordinal < op.ordinal => i < 0,
	 *         this.ordinal = op.ordinal => i = 0, i > 0
	 * @throws NullPointerException  op = null
	 */
	public int compareTo(Operator op) {
		return ordinal() - op.ordinal();
	}
	
	/**
	 * N-ary {@link MultiGate AND} operator.
	 */
	public static final Nary AND = new Nary(0) {
		public String toString() { return "&"; }
		/** @return true */
		public BooleanConstant identity() { return BooleanConstant.TRUE; }
		/** @return false */
		public BooleanConstant shortCircuit() { return BooleanConstant.FALSE; }
		/** @return OR */
		public Nary complement() {  return OR; }
	};
	
	/**
	 * N-ary {@link MultiGate OR} operator.
	 */
	public static final Nary OR = new Nary(1) {
		public String toString() { return "|"; }
		/** @return false */
		public BooleanConstant identity() { return BooleanConstant.FALSE; }
		/** @return true */
		public BooleanConstant shortCircuit() { return BooleanConstant.TRUE; }
		/** @return AND */
		public Nary complement() {  return AND; }
	};
	
	/**
	 * Ternary {@link ITEGate if-then-else} operator.
	 */
	public static final Ternary ITE = new Ternary(2) {
		public String toString() { return "?"; }
	};
	
	/**
	 * Unary {@link NotGate negation} operator.
	 */
	public static final Operator NOT = new Operator(3) {
		public String toString() { return "!"; }
	};
	
	/**
	 * Zero-arity {@link BooleanVariable variable} operator.  
	 */
	public static final Operator VAR = new Operator(4) {
		public String toString() { return "var"; }
	};
	
	/**
	 * Zero-arity {@link BooleanConstant constant} operator.  
	 */
	public static final Operator CONST = new Operator(5) {
		public String toString() { return "const"; }
	};
	
	/**
	 * An n-ary operator, where n>=2
	 */
	public static abstract class Nary extends Operator {
		
		private Nary(int ordinal) {
			super(ordinal);
		}
		
		/**
		 * Returns the hashcode for a gate v such that
		 * v.op = this && v.inputs[int] = f0 + f1
		 * @return f0.hash(this) + f1.hash(this)
		 */
		int hash(BooleanFormula f0, BooleanFormula f1) {
			return f0.hash(this) + f1.hash(this);
		}
		
		/**
		 * Returns the hashcode for a gate v such that
		 * v.op = this && v.iterator() = formulas.
		 * @return sum(formulas.hash(this))
		 */
		int hash(Iterator<BooleanFormula> formulas) {
			int sum = 0;
			while(formulas.hasNext())
				sum += formulas.next().hash(this);
			return sum;
		}
		
		/**
		 * Returns the boolean constant <i>c</i> such that 
		 * for all logical values <i>x</i>, <i>c</i> composed
		 * with <i>x</i> using this operator will result in <i>x</i>.
		 * @return the identity value of this binary operator
		 */
		public abstract BooleanConstant identity();
		/**
		 * Returns the boolean constant <i>c</i> such that 
		 * for all logical values <i>x</i>, <i>c</i> composed
		 * with <i>x</i> using this operator will result in <i>c</i>.
		 * @return the short circuiting value of this binary operator
		 */
		public abstract BooleanConstant shortCircuit();
		/**
		 * Returns the binary operator whose identity and short circuit
		 * values are the negation of this operator's identity and
		 * short circuit.
		 * @return the complement of this binary operator
		 */
		public abstract Operator.Nary complement();
	}
	
	static abstract class Ternary extends Operator {
		
		private Ternary(int ordinal) {
			super(ordinal);
		}
		
		/**
		 * Returns the hashcode for a gate v such that
		 * v = (i ? t : e)
		 * @return 3*i.hash(this) + 5*t.hash(this) + 7*e.hash(this)
		 */
		int hash(BooleanFormula i, BooleanFormula t, BooleanFormula e) {
			return 3*i.hash(this) + 5*t.hash(this) + 7*e.hash(this);
		}
	}
	
}
