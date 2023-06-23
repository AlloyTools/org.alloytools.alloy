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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.ast;

import static kodkod.ast.operator.FormulaOperator.AND;
import static kodkod.ast.operator.FormulaOperator.IFF;
import static kodkod.ast.operator.FormulaOperator.IMPLIES;
import static kodkod.ast.operator.FormulaOperator.OR;
import static kodkod.ast.operator.Quantifier.ALL;
import static kodkod.ast.operator.Quantifier.SOME;
import static kodkod.ast.operator.TemporalOperator.ALWAYS;
import static kodkod.ast.operator.TemporalOperator.EVENTUALLY;
import static kodkod.ast.operator.TemporalOperator.HISTORICALLY;
import static kodkod.ast.operator.TemporalOperator.AFTER;
import static kodkod.ast.operator.TemporalOperator.ONCE;
import static kodkod.ast.operator.TemporalOperator.BEFORE;
import static kodkod.ast.operator.TemporalOperator.RELEASES;
import static kodkod.ast.operator.TemporalOperator.SINCE;
import static kodkod.ast.operator.TemporalOperator.TRIGGERED;
import static kodkod.ast.operator.TemporalOperator.UNTIL;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;

import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.util.collections.Containers;

/**
 * A first-order formula. Unless otherwise noted,
 * all methods in this class throw a NullPointerException when given
 * null arguments.
 * @author Emina Torlak 
 * @modified Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public abstract class Formula extends Node {
	
	/** Constant formula true */
	public static final Formula TRUE = new ConstantFormula(true) {};
	
	/** Constant formula false */
	public static final Formula FALSE = new ConstantFormula(false) {};
	
    Formula() {}

    /**
     * Returns the constant formula with the given value.
     * @return value ? TRUE : FALSE
     */
    public static Formula constant(boolean value) { return value ? TRUE : FALSE; }
    
    /**
     * Returns the conjunction of this and the specified formula. The effect
     * of this method is the same as calling this.compose(AND, formula).
     * @return this.compose(AND, formula)
     */
    public final Formula and(Formula formula) {
        return compose(AND,formula);
    }
    
    /**
     * Returns the conjunction of this and the specified formula. The effect
     * of this method is the same as calling this.compose(OR, formula).
     * @return this.compose(OR, formula)
     */
    public final Formula or(Formula formula) {
        return compose(OR,formula);
    }
    
    /**
     * Returns a formula that equates this and the specified formula. The effect
     * of this method is the same as calling this.compose(IFF, formula).
     * @return this.compose(IFF, formula)
     */
    public final Formula iff(Formula formula) {
        return compose(IFF,formula);
    }
    
    /**
     * Returns the implication of the specified formula by this. The effect
     * of this method is the same as calling this.compose(IMPLIES, formula).
     * @return this.compose(IMPLIES, formula)
     */
    public final Formula implies(Formula formula) {
        return compose(IMPLIES,formula);
    }

    
    /**
     * Returns the composition of this and the specified formula using the
     * given binary operator.
     * @return {f: Formula | f.left = this and f.right = formula and f.op = op }
     */
    public final Formula compose(FormulaOperator op, Formula formula) {
    	return new BinaryFormula(this, op, formula);
    }
    
    /**
     * Returns the composition of this and the specified formula using the
     * given binary temporal operator.
     * @return {f: Formula | f.left = this and f.right = formula and f.op = op }
     */
    // [HASLab]
    public final Formula compose(TemporalOperator op, Formula formula) {
    	return new BinaryTempFormula(this, op, formula);
    }
    
    /**
     * Returns the conjunction of the given formulas. The effect of this method is the
     * same as calling compose(AND, formulas).
     * @return compose(AND, formulas)
     */
    public static Formula and(Formula...formulas) { 
    	return compose(AND, formulas);
    }
    
    /**
     * Returns the conjunction of the given formulas. The effect of this method is the
     * same as calling compose(AND, formulas).
     * @return compose(AND, formulas)
     */
    public static Formula and(Collection<? extends Formula> formulas) { 
    	return compose(AND, formulas);
    }
    
    /**
     * Returns the disjunction of the given formulas. The effect of this method is the
     * same as calling compose(OR, formulas).
     * @return compose(OR, formulas)
     */
    public static Formula or(Formula...formulas) { 
    	return compose(OR, formulas);
    }
    
    /**
     * Returns the disjunction of the given formulas. The effect of this method is the
     * same as calling compose(OR, formulas).
     * @return compose(OR, formulas)
     */
    public static Formula or(Collection<? extends Formula> formulas) { 
    	return compose(OR, formulas);
    }
    
    /**
     * Returns the composition of the given formulas using the given operator. 
     * @requires formulas.length != 2 => op.nary()
     * @return 
     * <pre> 
     *  formulas.length = 0 => constant(op=AND) else
     * 	formulas.length=1 => formulas[0] else 
     *  {e: Formula | e.children = formulas and e.op = this }
     * </pre>
     */
    public static Formula compose(FormulaOperator op, Formula...formulas) { 
    	switch(formulas.length) { 
    	case 0 : 	
    		switch(op) { 
    		case AND : return TRUE;
    		case OR : return FALSE;
    		default : throw new IllegalArgumentException("Expected at least one argument: " + Arrays.toString(formulas));
    		}
    	case 1 : 	return formulas[0];
    	case 2 : 	return new BinaryFormula(formulas[0], op, formulas[1]);
    	default : 	return new NaryFormula(op, Containers.copy(formulas, new Formula[formulas.length]));
    	}
    }
    
    /**
     * Returns the composition of the given formulas using the given operator. 
     * @requires formulas.size() != 2 => op.nary()
     * @return 
     * <pre> 
     *  formulas.size() = 0 => constant(op=AND) else
     *  formulas.size() = 1 => formulas.iterator().next() else 
     *  {e: Formula | e.children = formulas.toArray() and e.op = this }
     * </pre>
     */
    public static Formula compose(FormulaOperator op, Collection<? extends Formula> formulas) { 
    	switch(formulas.size()) { 
    	case 0 : 	
    		switch(op) { 
    		case AND : return TRUE;
    		case OR : return FALSE;
    		default : throw new IllegalArgumentException("Expected at least one argument: " + formulas);
    		}
    	case 1 : 	return formulas.iterator().next();
    	case 2 :
    		final Iterator<? extends Formula> itr = formulas.iterator();
    		return new BinaryFormula(itr.next(), op, itr.next());
    	default : 			
    		return new NaryFormula(op, formulas.toArray(new Formula[formulas.size()]));
    	}
    }
    
    /**
     * Returns the composition of the given formulas using the given temporal operator. 
     * @requires formulas.length = 2 => op.binary(), formulas.length = 1 => op.unary()
     * @return formulas.length=1 => formulas.iterator().next() else {e: Expression | e.children = formulas.toArray() and e.op = this }
     */
    // [HASLab]
    public static Formula compose(TemporalOperator op, Collection<? extends Formula> formulas) { 
    	switch(formulas.size()) { 
    	case 0 :  throw new IllegalArgumentException("Expected at least one argument: " + formulas);
    	case 1 :  return new UnaryTempFormula(op, formulas.iterator().next());
    	case 2 :
    		final Iterator<? extends Formula> itr = formulas.iterator();
    		return new BinaryTempFormula(itr.next(), op, itr.next());
    	default : throw new IllegalArgumentException("Expected unary or binary formula: " + formulas);
    	}
    }
    
    /**
     * Returns the composition of the given formulas using the given temporal operator. 
     * @requires formulas.length = 2 => op.binary(), formulas.length = 1 => op.unary()
     * @return formulas.length=1 => formulas[0] else {e: Expression | e.children = formulas and e.op = this }
     */
    // [HASLab]
    public static Formula compose(TemporalOperator op,  Formula...formulas) { 
    	switch(formulas.length) { 
    	case 0 :  throw new IllegalArgumentException("Expected at least one argument: " + Arrays.toString(formulas));
    	case 1 :  return new UnaryTempFormula(op, formulas[0]);
    	case 2 :  return new BinaryTempFormula(formulas[0], op, formulas[1]);
    	default : throw new IllegalArgumentException("Expected unary or binary formula: " + Arrays.toString(formulas));
    	}
    }
    
    /**
     * Returns the formula that results from applying the given temporal unary operator
     * to this. 
     * @requires op.unary()
     * @return {e: Expression | e.formula = this && e.op = this }
     * @throws IllegalArgumentException  this.arity != 1
     */
    // [HASLab]
    public final Formula apply(TemporalOperator op) {
    	return new UnaryTempFormula(op, this);
    }

    /**
     * Returns a formula that represents a universal quantification of this
     * formula over the given declarations. The effect of this method is the same 
     * as calling this.quantify(ALL, decls).
     * @return this.quantify(ALL, decls)
     */
    public final Formula forAll(Decls decls) {
    	return quantify(ALL, decls);
    }
    
    /**
     * Returns a formula that represents an existential quantification of this
     * formula over the given declarations. The effect of this method is the same 
     * as calling this.quantify(SOME, decls).
     * @return this.quantify(SOME, decls)
     */
    public final Formula forSome(Decls decls) {
    	return quantify(SOME, decls);
    }
    
    /**
     * Returns a quantification of this formula using the given quantifier over 
     * the specified declarations. 
     * @return {f: Formula | f.decls = decls and f.formula = this and f.quantifier = quantifer }
     */
    public final Formula quantify(Quantifier quantifier, Decls decls) {
    	return new QuantifiedFormula(quantifier, decls, this);
    }
    
    /**
     * Returns the comprehension expression constructed from this formula and
     * the given declarations.
     * @requires all d: decls.decls[int] | decl.variable.arity = 1 and decl.multiplicity = ONE
     * @return {e: Expression | e.decls = decls and e.formula = this }
     */
    public final Expression comprehension(Decls decls) {
    	return new Comprehension(decls,this);
    }
    
    /**
     * Returns the if expression constructed from this formula and the
     * specified then and else expressions.
     * @return {e: Expression | e.condition = this and e.thenExpr = thenExpr and e.elseExpr = elseExpr}
     */
    public final Expression thenElse(Expression thenExpr, Expression elseExpr) {
    	return new IfExpression(this, thenExpr, elseExpr);
    }
    
    /**
     * Returns the if expression constructed from this formula and the
     * specified then and else integer expressions.
     * @return {e: IntExpression | e.condition = this and e.thenExpr = thenExpr and e.elseExpr = elseExpr}
     */
    public final IntExpression thenElse(IntExpression thenExpr, IntExpression elseExpr) {
    	return new IfIntExpression(this, thenExpr, elseExpr);
    }
    
    /**
     * Returns the negation of this formula.
     * @return {f : NotFormula | f.formula = this }
     */
    public final Formula not() {
        return new NotFormula(this);
    }
    
    /**
     * Returns this quantified with after. The effect of this method is the same
     * as calling this.apply(AFTER).
     * @return this.apply(AFTER)
     */
    // [HASLab]
    public final Formula after() {
        return apply(AFTER);
    }
    
    /**
     * Returns this quantified with always. The effect of this method is the same
     * as calling this.apply(ALWAYS).
     * @return this.apply(ALWAYS)
     */
    // [HASLab]
    public final Formula always() {
        return apply(ALWAYS);
    }

    /**
     * Returns this quantified with eventually. The effect of this method is the same
     * as calling this.apply(EVENTUALLY).
     * @return this.apply(EVENTUALLY)
     */
    // [HASLab]
    public final Formula eventually() {
        return apply(EVENTUALLY);
    }
    
    /**
     * Returns this quantified with before. The effect of this method is the same
     * as calling this.apply(BEFORE).
     * @return this.apply(BEFORE)
     */
    // [HASLab]
    public final Formula before() {
        return apply(BEFORE);
    }
    
    /**
     * Returns this quantified with historically. The effect of this method is the same
     * as calling this.apply(HISTORICALLY).
     * @return this.apply(HISTORICALLY)
     */
    // [HASLab]
    public final Formula historically() {
        return apply(HISTORICALLY);
    }

    /**
     * Returns this quantified with once. The effect of this method is the same
     * as calling this.apply(ONCE).
     * @return this.apply(ONCE)
     */
    // [HASLab]
    public final Formula once() {
        return apply(ONCE);
    }

    /**
     * Composes this and the specified formula with until. The effect
     * of this method is the same as calling this.compose(UNTIL, formula).
     * @return this.compose(UNTIL, formula)
     */
    // [HASLab]
    public final Formula until(Formula formula) {
        return compose(UNTIL, formula);
    }

    /**
     * Composes this and the specified formula with releases. The effect
     * of this method is the same as calling this.compose(RELEASES, formula).
     * @return this.compose(RELEASES, formula)
     */
    // [HASLab]
    public final Formula releases(Formula formula) {
        return compose(RELEASES, formula);
    }

    /**
     * Composes this and the specified formula with triggered. The effect
     * of this method is the same as calling this.compose(TRIGGERED, formula).
     * @return this.compose(TRIGGERED, formula)
     */
    // [HASLab]
    public final Formula triggered(Formula formula) {
        return compose(TRIGGERED, formula);
    }

    /**
     * Composes this and the specified formula with since. The effect
     * of this method is the same as calling this.compose(SINCE, formula).
     * @return this.compose(SINCE, formula)
     */
    // [HASLab]
    public final Formula since(Formula formula) {
        return compose(SINCE, formula);
    }

    /**
     * Accepts the given visitor and returns the result.
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    public abstract <E, F, D, I> F accept(ReturnVisitor<E, F, D, I> visitor);
}
