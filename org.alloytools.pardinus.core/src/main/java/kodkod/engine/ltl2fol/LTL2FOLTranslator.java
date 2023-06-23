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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.Variable;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.AbstractReplacer;

import static kodkod.engine.ltl2fol.TemporalTranslator.L_FIRST;
import static kodkod.engine.ltl2fol.TemporalTranslator.L_LAST;
import static kodkod.engine.ltl2fol.TemporalTranslator.L_PREFIX;
import static kodkod.engine.ltl2fol.TemporalTranslator.LEVEL;
import static kodkod.engine.ltl2fol.TemporalTranslator.FIRST;
import static kodkod.engine.ltl2fol.TemporalTranslator.LAST;
import static kodkod.engine.ltl2fol.TemporalTranslator.LAST_;
import static kodkod.engine.ltl2fol.TemporalTranslator.LOOP;
import static kodkod.engine.ltl2fol.TemporalTranslator.PREFIX;
import static kodkod.engine.ltl2fol.TemporalTranslator.STATE;
import static kodkod.engine.ltl2fol.TemporalTranslator.TRACE;
import static kodkod.engine.ltl2fol.TemporalTranslator.UNROLL_MAP;
import static kodkod.engine.ltl2fol.TemporalTranslator.START;

/**
 * Translates an LTL temporal formula into its standard Kodkod FOL
 * representation. Assumes that the variable relations have been previously
 * expanded into its static version. To do so, it explicitly introduces the time
 * elements into the formula, converting the temporal operators into time
 * quantifiers and applying the time variable to variable relations. Since
 * global temporal quantifications force the trace to be infinite, the formula
 * must be in negative normal form to guarantee a correct translation.
 * 
 * As of Pardinus 1.1, traces are assumed to always loop.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class LTL2FOLTranslator extends AbstractReplacer {

	private Set<Relation> vars_found;
	private Map<Formula,Formula> inv_cache = new HashMap<>();

	/** Pre-computed information about the formula, allows optimizations. */
	private boolean has_past;

	/**
	 * Translates an LTL temporal formula into its standard Kodkod FOL
	 * representation, given the extension of the variable relations.
	 * 
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 */
	private LTL2FOLTranslator(boolean has_past) {
		super(new HashSet<Node>());
		this.has_past = has_past;
		this.vars_found = new HashSet<Relation>();
	}
	
	@Override
	protected <N extends Node> N cache(N node, N replacement) {
		if (cached.contains(node)) {
			cache.put(node, replacement);
		}
		if (node instanceof Formula)
			inv_cache.put((Formula) replacement, (Formula) node);
		return replacement;
	}

	/**
	 * Converts an LTL temporal formula into a regular Kodkod FOL formula. Uses the
	 * visitor to convert and adds any trace constraint left at the top level to
	 * handle nested post operators. It also adds the constraints that define the
	 * structure of the time relation constants. This is the main method that should
	 * be called to convert temporal formulas. The formula should be in negative
	 * normal form in order for the temporal quantifiers to be correctly translated.
	 * Optimizations will be applied if the the formula is known to force a loop or
	 * has no past operators.
	 * 
	 * @param form
	 *            the LTL formula to be converted.
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param tempTransLog
	 * 			  map logging the translation of top-level formulas.
	 * @return the resulting FOL formula.
	 */
	public static Formula translate(Formula form, int state, boolean has_past, Map<Formula,Formula> tempTransLog) {
		LTL2FOLTranslator translator = new LTL2FOLTranslator(has_past);

		Formula f;
		
		if (TemporalTranslator.ExplicitUnrolls) {

			Variable v = Variable.unary("v");
			Formula order_unr_trace1 = v.join(PREFIX).one().forAll(v.oneOf(STATE.difference(LAST)));
			Formula order_unr_trace2 = PREFIX.join(v).one().forAll(v.oneOf(STATE.difference(FIRST)));
			Formula order_unr_trace3 = FIRST.join(PREFIX.reflexiveClosure()).eq(STATE);
			Formula order_unr_trace4 = PREFIX.in(STATE.product(STATE));
			
			if (has_past) {
				Variable v1 = Variable.unary("v1");
				// all s0, s1
				order_unr_trace3 = order_unr_trace3.and((v.join(UNROLL_MAP).eq(v1.join(UNROLL_MAP)).implies(v.join(TRACE).join(UNROLL_MAP).eq(v1.join(TRACE).join(UNROLL_MAP)))).forAll(v1.oneOf(LAST_.join(TRACE.reflexiveClosure()))).forAll(v.oneOf(LAST_.join(TRACE.reflexiveClosure()))));
			}

			Formula loopDecl_unr = LOOP.one();
			
			f = Formula.and(order_unr_trace1, order_unr_trace2, order_unr_trace3, order_unr_trace4, loopDecl_unr);
		} else {
			// TotalOrder(S/Next,State,S/First,S/Last)
			Formula st = PREFIX.totalOrder(STATE, FIRST, LAST);
			// TotalOrder(L/Next,Level,L/First,L/Last)
			Formula lv = L_PREFIX.totalOrder(LEVEL, L_FIRST, L_LAST);
			
			Formula loopDecl_unr = LOOP.one();
			
			f = Formula.and(st,lv,loopDecl_unr);
		}
		
		translator.pushLevel();
		translator.pushVariable(state);

		// log translation of formulas
		Formula tfrm =form.accept(translator);
		tempTransLog.putAll(translator.inv_cache);
		
		Formula hack = Formula.TRUE;
		if (!TemporalTranslator.ExplicitUnrolls) {
			for (Relation r : translator.vars_found)
				// r.(loop.prev) = r.last
				hack = hack.and(r.join(LOOP.join(PREFIX.transpose())).eq(r.join(LAST)));
		}
		
		return Formula.and(f,tfrm,hack);
	}

	/**
	 * Converts an LTL temporal expression into a regular Kodkod FOL expression in a
	 * concrete time step, counting from the {@link TemporalTranslator#FIRST
	 * initial} time. Uses the visitor to convert. This is the main method that
	 * should be called to convert temporal expressions.
	 * 
	 * @param expr
	 *            the LTL expression to be converted.
	 * @param state
	 *            the concrete state on which to evaluate the expression.
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 * @return the resulting static expression.
	 */
	public static Expression translate(Expression expr, int state, boolean has_past) {
		LTL2FOLTranslator translator = new LTL2FOLTranslator(has_past);

		translator.pushVariable(state);

		Expression result = expr.accept(translator);

		return result;
	}
	
	/**
	 * Converts an LTL temporal int expression into a regular Kodkod FOL int expression 
	 * in a concrete time step, counting from the {@link TemporalTranslator#FIRST
	 * initial} time. Uses the visitor to convert. This is the main method that
	 * should be called to convert temporal int expressions.
	 * 
	 * @param expr
	 *            the LTL expression to be converted.
	 * @param state
	 *            the concrete state on which to evaluate the expression.
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 * @return the resulting static expression.
	 */
	public static IntExpression translate(IntExpression expr, int state, boolean has_past) {
		LTL2FOLTranslator translator = new LTL2FOLTranslator(has_past);

		translator.pushVariable(state);

		IntExpression result = expr.accept(translator);

		return result;
	}

	@Override
	public Expression visit(ConstantExpression constant) {
		Expression eu = STATE;
		final Expression res;
		if (has_past) eu = UNROLL_MAP.join(STATE);
		if (constant.equals(Expression.UNIV))
			res = constant.difference(eu);
		else if (constant.equals(Expression.IDEN)) 
			res = constant.difference(eu.product(eu));
		else
			res = constant;
		return cache(constant, res);
	}

	@Override
	public Expression visit(Relation relation) {
		final Expression res;
		if (relation.isVariable()) {
			if (has_past && TemporalTranslator.ExplicitUnrolls)
				res = relation.getExpansion().join(getVariable().join(UNROLL_MAP));
			else {
				if (has_past) vars_found.add(relation.getExpansion());
				res = relation.getExpansion().join(getVariable());
			}
		} else
			res = relation;
		return cache(relation, res);
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (TemporalTranslator.isTemporal(relationPredicate))
			// cannot simply expand since it would loose symmetry breaking
			// return relationPredicate.toConstraints().always().accept(this);
			throw new InvalidMutableExpressionException(relationPredicate);

		return cache(relationPredicate,relationPredicate);
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		pushOperator(unaryTempFormula.op());
		pushLevel();
		pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = getQuantifier(getOperator(), e);
		popOperator();
		popVariable();
		popLevel();
		return cache(unaryTempFormula,rt);
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		pushOperator(binaryTempFormula.op());
		pushLevel();
		pushVariable();
		Formula rt, left, right;
		switch (binaryTempFormula.op()) {
		case UNTIL:
			right = binaryTempFormula.right().accept(this);
			pushVariable();
			left = binaryTempFormula.left().accept(this);
			rt = getQuantifierUntil(left, right);
			popVariable();
			break;
		case SINCE:
			right = binaryTempFormula.right().accept(this);
			pushVariable();
			left = binaryTempFormula.left().accept(this);
			rt = getQuantifierSince(left, right);
			popVariable();
			break;
		case RELEASES:
			Formula rightAlways = binaryTempFormula.right().accept(this);
			pushVariable();
			left = binaryTempFormula.left().accept(this);
			pushLevel();
			pushVariable();
			right = binaryTempFormula.right().accept(this);
			rt = getQuantifierRelease(rightAlways, left, right);
			popVariable();
			popLevel();
			popVariable();
			break;
		case TRIGGERED:
			rightAlways = binaryTempFormula.right().accept(this);
			pushVariable();
			left = binaryTempFormula.left().accept(this);
			pushLevel();
			pushVariable();
			right = binaryTempFormula.right().accept(this);
			rt = getQuantifierTrigger(rightAlways, left, right);
			popVariable();
			popLevel();
			popVariable();
			break;
		default:
			throw new UnsupportedOperationException("Unsupported binary temporal operator:" + binaryTempFormula.op());
		}
		popVariable();
		popLevel();
		popOperator();
		return cache(binaryTempFormula,rt);
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		pushOperator(tempExpression.op());
		pushVariable();
		Expression rt = tempExpression.expression().accept(this);
		popOperator();
		popVariable();
		return cache(tempExpression,rt);
	}

	private Formula getQuantifier(TemporalOperator op, Formula e) {
		Variable s1;
		Expression s0 = getVariablePrevQuant();
		if (TemporalTranslator.ExplicitUnrolls) {
			switch (op) {
			case ALWAYS:
				s1 = (Variable) getVariable();
				return e.forAll(s1.oneOf(s0.join(TRACE.reflexiveClosure())));
			case EVENTUALLY:
				s1 = (Variable) getVariable();
				return e.forSome(s1.oneOf(s0.join(TRACE.reflexiveClosure())));
			case HISTORICALLY:
				s1 = (Variable) getVariable();
				return e.forAll(s1.oneOf(s0.join(PREFIX.transpose().reflexiveClosure())));
			case ONCE:
				s1 = (Variable) getVariable();
				return e.forSome(s1.oneOf(s0.join(PREFIX.transpose().reflexiveClosure())));
			case BEFORE:
				Expression v2 = getVariable();
				e = v2.some().and(e);
				return e;
			default:
				return e;
			} 
		} else {
			Variable l1;
			Expression l0 = getLevelPrevQuant();
			switch (op) {
			case ALWAYS:
				s1 = (Variable) getVariable();
				l1 = (Variable) getLevel();
				Expression rng;
				// (l1 = l0 && l1 != last) => s0.*next else State
				rng = (l1.eq(l0).and(l1.eq(L_LAST).not())).thenElse(s0.join(PREFIX.reflexiveClosure()),STATE);
				// l1.start.*trace & ((l1 = l0 || l1 = last) => s0.*next else State)
				rng = rng.intersection(l1.join(START).join(PREFIX.reflexiveClosure()));
				// all l1 : l0.*next, s1 : (l1.start.*next & ((l1 = l0 || l1 = last) => s0.*next else State)) | e
				return e.forAll(s1.oneOf(rng)).forAll(l1.oneOf(l0.join(L_PREFIX.reflexiveClosure())));
			case EVENTUALLY:
				s1 = (Variable) getVariable();
				l1 = (Variable) getLevel();
				// (l1 = l0 && l1 != last) => s0.*next else State
				rng = (l1.eq(l0).and(l1.eq(L_LAST).not())).thenElse(s0.join(PREFIX.reflexiveClosure()),STATE);
				// l1.start.*trace & ((l1 = l0 || l1 = last) => s0.*next else State)
				rng = rng.intersection(l1.join(START).join(PREFIX.reflexiveClosure()));
				// some l1 : l0.*next, s1 : (l1.start.*next & ((l1 = l0 || l1 = last) => s0.*next else State)) | e
				return e.forSome(s1.oneOf(rng)).forSome(l1.oneOf(l0.join(L_PREFIX.reflexiveClosure())));
			case HISTORICALLY:
				s1 = (Variable) getVariable();
				l1 = (Variable) getLevel();
				// l1 = l0 => s0.*prev else State
				rng = l1.eq(l0).thenElse(s0.join(PREFIX.transpose().reflexiveClosure()),STATE);
				// l1.start.*prev & (l1 = l0 => s0.*prev else State)
				rng = rng.intersection(l1.join(START).join(PREFIX.reflexiveClosure()));
				// all l1 : l0.*prev, s1 : l1.start.*prev & (l1 = l0 => s0.*prev else State) | e
				return e.forAll(s1.oneOf(rng)).forAll(l1.oneOf(l0.join(L_PREFIX.transpose().reflexiveClosure())));
			case ONCE:
				s1 = (Variable) getVariable();
				l1 = (Variable) getLevel();
				// l1 = l0 => s0.*prev else State
				rng = l1.eq(l0).thenElse(s0.join(PREFIX.transpose().reflexiveClosure()),STATE);
				// l1.start.*prev & (l1 = l0 => s0.*prev else State)
				rng = rng.intersection(l1.join(START).join(PREFIX.reflexiveClosure()));
				// some l1 : l0.*prev, s1 : l1.start.*prev & (l1 = l0 => s0.*prev else State) | e
				return e.forSome(s1.oneOf(rng)).forSome(l1.oneOf(l0.join(L_PREFIX.transpose().reflexiveClosure())));
			case BEFORE:
				// (s0 = loop && l0 != first) => last else s0.prev
				Expression s0n = getVariable();
				// (s0 = loop && l0 != first) => l0.prev else l0
				Expression l0n = getLevel();
				// some (s0 = loop && l0 != first) => last else s0.prev && e
				e = s0n.some().and(e);
				return e;
			default:
				return e;
			}
		}
	}

	private Formula getQuantifierUntil(Formula left, Formula right) {
		
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Expression prev_l = getVariablePrevQuantUntil(false);
		if (TemporalTranslator.ExplicitUnrolls) {
			Formula nfleft = left.forAll(l.oneOf(upTo(prev_l, r, false)));
			
			nfleft = right.and(nfleft);
			
			return nfleft.forSome(r.oneOf(prev_l.join(TRACE.reflexiveClosure())));
		}
		else {
			Variable vl = getLevelUntil();
			Expression prev_vl = getLevelPrevQuantUntil();

			Expression rng1 = (vl.eq(prev_vl.join(L_PREFIX))).thenElse(r.join(PREFIX.transpose().closure()), STATE);
			Expression rng0 = (vl.eq(prev_vl)).thenElse(upTo(prev_l, r, false),prev_l.join(PREFIX.reflexiveClosure()).union((vl.join(START).join(PREFIX.reflexiveClosure()).intersection(rng1))));
			
			Formula nfleft = left.forAll(l.oneOf(rng0));
			
			nfleft = right.and(nfleft);
			
			Expression rng = vl.eq(prev_vl).thenElse(prev_l.join(PREFIX.reflexiveClosure()),STATE);

			return nfleft.forSome(r.oneOf(rng.intersection(vl.join(START).join(TRACE.reflexiveClosure())))).forSome(vl.oneOf(prev_vl.join(L_PREFIX.reflexiveClosure())));
		}
	}

	private Formula getQuantifierSince(Formula left, Formula right) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Expression prev_l = getVariablePrevQuantUntil(false);
		
		if (TemporalTranslator.ExplicitUnrolls) {

			Formula nfleft = left.forAll(l.oneOf(downTo(prev_l, r, false)));
	
			nfleft = right.and(nfleft);
	
			return nfleft
					.forSome(r.oneOf(prev_l.join(PREFIX.transpose().reflexiveClosure())));
		} else {

			Variable vl = getLevelUntil();
			Expression prev_vl = getLevelPrevQuantUntil();

			
			Expression rng1 = (prev_vl.eq(vl.join(L_PREFIX))).thenElse(prev_l.join(PREFIX.transpose().reflexiveClosure()), STATE);
			Expression rng0 = (vl.eq(prev_vl)).thenElse(downTo(prev_l, r, false),r.join(PREFIX.closure()).union((prev_vl.join(START).join(PREFIX.reflexiveClosure()).intersection(rng1))));
			
			Formula nfleft = left.forAll(l.oneOf(rng0));
			
			nfleft = right.and(nfleft);
			
			Expression rng = vl.eq(prev_vl).thenElse(prev_l.join(PREFIX.transpose().reflexiveClosure()),STATE);

			return nfleft.forSome(r.oneOf(rng.intersection(vl.join(START).join(PREFIX.reflexiveClosure())))).forSome(vl.oneOf(prev_vl.join(L_PREFIX.transpose().reflexiveClosure())));
		}
	}

	private Formula getQuantifierRelease(Formula always, Formula left, Formula right) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;
	
		if (TemporalTranslator.ExplicitUnrolls) {
			alw = always.forAll(v.oneOf(getVariablePrevQuantRelease(false, true).join(TRACE.reflexiveClosure())));
		
			nfleft = right.forAll(l.oneOf(upTo(getVariablePrevQuantRelease(false, true), r, true)));
		
			nfright = left.and(nfleft);
		
			nfright = nfright
					.forSome(r.oneOf(getVariablePrevQuantRelease(false, true).join(TRACE.reflexiveClosure())));
		
			return alw.or(nfright); }
		else 
			throw new UnsupportedOperationException("Releases for alterative past encoding.");
	}
	
	private Formula getQuantifierTrigger(Formula always, Formula left, Formula right) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;
	
		if (TemporalTranslator.ExplicitUnrolls) {
			alw = always.forAll(v.oneOf(getVariablePrevQuantRelease(false, true).join(PREFIX.transpose().reflexiveClosure())));
		
			nfleft = right.forAll(l.oneOf(downTo(getVariablePrevQuantRelease(false, true), r, true)));
		
			nfright = left.and(nfleft);
		
			nfright = nfright
					.forSome(r.oneOf(getVariablePrevQuantRelease(false, true).join(PREFIX.transpose().reflexiveClosure())));
		
			return alw.or(nfright);
		}
		else 
			throw new UnsupportedOperationException("Triggered for alterative past encoding.");
	}
	
	/**
	 * An expression representing all states between two states, considering loops.
	 * 
	 * @param t1
	 *            the expression representing the lower state
	 * @param t2
	 *            the expression representing the upper state
	 * @param inc1
	 *            whether lower inclusive
	 * @param inc2
	 *            whether upper inclusive
	 * @return the expression representing the range states
	 */
	private Expression upTo(Expression t1, Expression t2, boolean inc2) {
		Formula c = t2.in(t1.join(PREFIX.reflexiveClosure()));
		Expression exp1 = PREFIX.reflexiveClosure();
		Expression exp2 = PREFIX.closure();
		Expression exp11 = TRACE.reflexiveClosure();
		Expression exp12 = TRACE.closure();
		Expression e1 = (t1.join(exp1)).intersection(t2.join(exp2.transpose()));
		Expression e21 = (t1.join(exp11)).intersection(t2.join(exp12.transpose()));
		Expression e22 = (t2.join(exp1)).intersection(t1.join(exp2.transpose()));
		Expression e2 = e21.difference(e22);
		Expression e = c.thenElse(e1, e2);
		if (inc2) e = e.union(t2); 
		return e;
	}
	
	private Expression downTo(Expression t1, Expression t2, boolean inc2) {
		Expression exp1 = PREFIX.reflexiveClosure();
		Expression exp2 = PREFIX.closure();
		Expression e1 = (t1.join(exp1.transpose())).intersection(t2.join(exp2));
		Expression e = e1;
		if (inc2) e = e.union(t2); 
		return e;
	}

	/* Operators Context */
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();

	private void pushOperator(TemporalOperator op) {
		operators.add(op);
	}

	private TemporalOperator getOperator() {
		return operators.get(operators.size() - 1);
	}

	private void popOperator() {
		operators.remove(operators.size() - 1);
	}

	/* Variables */
	private List<Expression> variables = new ArrayList<Expression>();
	private List<Expression> variables_lvl = new ArrayList<Expression>();
	private int vars = 0;

	private void pushVariable() {
		if (variables.isEmpty()) {
			variables.add(FIRST);
			return;
		}

		switch (getOperator()) {
		case AFTER:
		case PRIME:
			if (TemporalTranslator.ExplicitUnrolls)
				variables.add(getVariable().join(TRACE));
			else 
				// s0.trace
				variables.add(getVariable().join(TRACE));
			break;
		case BEFORE:
			if (TemporalTranslator.ExplicitUnrolls)
				variables.add(getVariable().join(PREFIX.transpose()));
			else 
				// (s0 = loop && l0 != first) => last else s0.prev
				variables.add((getVariable().eq(LOOP).and(getLevelPrevQuant().eq(L_FIRST).not())).thenElse(LAST,getVariable().join(PREFIX.transpose())));
			break;
		default:
			Variable v = Variable.unary("t" + vars);
			variables.add(v);
			vars++;
		}
	}

	private void pushLevel() {
		if (variables_lvl.isEmpty()) {
			variables_lvl.add(L_FIRST);
			return;
		}

		switch (getOperator()) {
		case AFTER:
		case PRIME:
			// (s0 = last && l0 != last) => l0.next else l0
			variables_lvl.add((getVariable().eq(LAST).and(getLevel().eq(L_LAST).not())).thenElse(getLevel().join(L_PREFIX),getLevel()));
			break;
		case BEFORE:
			// (s0 = loop && l0 != first) => l0.prev else l0
			variables_lvl.add((getVariable().eq(LOOP).and(getLevel().eq(L_FIRST).not())).thenElse(getLevel().join(L_PREFIX.transpose()),getLevel()));
			break;
		default:
			Variable v = Variable.unary("l" + vars);
			variables_lvl.add(v);
		}
	}

	/**
	 * Used to initialize the translation at a time other than the initial one.
	 * 
	 * @param state
	 *            the step of the trace in which to start the translation.
	 */
	private void pushVariable(int state) {
		if (variables.isEmpty()) {
			Expression s = FIRST;
			for (int i = 0; i < state; i++)
				s = s.join(TRACE);
			variables.add(s);
		} else
			throw new UnsupportedOperationException("No more vars.");
	}

	private void popVariable() {
		variables.remove(variables.size() - 1);
	}

	private void popLevel() {
		variables_lvl.remove(variables_lvl.size() - 1);
	}

	private Expression getVariable() {
		return variables.get(variables.size() - 1);
	}

	private Expression getLevel() {
		return variables_lvl.get(variables_lvl.size() - 1);
	}

	private Expression getVariablePrevQuant() {
		return variables.get(variables.size() - 2);
	}

	private Expression getLevelPrevQuant() {
		return variables_lvl.get(variables_lvl.size() - 2);
	}

	private Variable getVariableUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return (Variable) variables.get(variables.size() - 1);
		} else {
			return (Variable) variables.get(variables.size() - 2);
		}
	}
	
	private Variable getLevelUntil() {
		return (Variable) variables_lvl.get(variables_lvl.size() - 1);
	}

	private Variable getVariableRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return (Variable) variables.get(variables.size() - 3);
		} else {
			if (!sideIsRight) {
				return (Variable) variables.get(variables.size() - 1);
			} else {
				return (Variable) variables.get(variables.size() - 2);
			}
		}
	}

	private Expression getVariablePrevQuantUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return variables.get(variables.size() - 3);
		} else {
			return variables.get(variables.size() - 2);
		}
	}
	
	private Expression getLevelPrevQuantUntil() {
		return variables_lvl.get(variables_lvl.size() - 2);
	}

	private Expression getVariablePrevQuantRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return variables.get(variables.size() - 4);
		} else {
			if (!sideIsRight) {
				return variables.get(variables.size() - 3);
			} else {
				return variables.get(variables.size() - 2);
			}
		}
	}

}
