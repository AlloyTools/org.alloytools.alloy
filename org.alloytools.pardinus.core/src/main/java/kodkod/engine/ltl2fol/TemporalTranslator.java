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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NaryIntExpression;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.Variable;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.RelationPredicate.Function;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.engine.config.Options;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Tuple;

/**
 * Expands temporal problems into plain problems, i.e., formulas with
 * {@link kodkod.ast.operator.TemporalOperator temporal operators} and bounds
 * over {@link kodkod.ast.VarRelation variable relations}, into regular Kodkod
 * static problems, i.e., standard {@link kodkod.ast.Formula formulas} and
 * {@link kodkod.instance.Bounds bounds}, following the provided
 * {@link kodkod.engine.config.TemporalOptions temporal options}.
 *
 * Relations are introduced to explicitly model the (bounded) temporal trace,
 * and variable relations are expanded to static ones that refer to that trace.
 * To provide sound loop bounded model checking semantics for past operators,
 * loops are unrolled according to the past operator depth.
 *
 * As of Pardinus 1.1, traces are assumed to always loop.
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalTranslator {
	
	public static final boolean ExplicitUnrolls = true;

	/** The name assigned to {@link #STATE state} atoms. */
	public static final String STATEATOM = "Time";

	/** Relations representing the explicit trace of the temporal problem. **/
	public static final Relation STATE = Relation.unary(STATEATOM);
	public static final Relation FIRST = Relation.unary("S/first");
	public static final Relation LAST = Relation.unary("S/last");
	public static final Relation PREFIX = Relation.binary("S/next");
	public static final Relation LOOP = Relation.unary("loop");
	public static final Expression TRACE = PREFIX.union(LAST.product(LOOP));

	public static final Relation LAST_ = Relation.unary("S/last_"); 			// ExplicitUnrolls = true
	public static final Relation UNROLL_MAP = Relation.binary("unroll_map"); 	// ExplicitUnrolls = true

	public static final Relation LEVEL = Relation.unary("Level"); 				// ExplicitUnrolls = false
	public static final Relation L_FIRST = Relation.unary("L/first"); 			// ExplicitUnrolls = false
	public static final Relation L_LAST = Relation.unary("L/last"); 			// ExplicitUnrolls = false
	public static final Relation L_PREFIX = Relation.binary("L/next"); 			// ExplicitUnrolls = false

	public static final String STATE_SEP = "_";

	public static final Expression START = L_FIRST.product(FIRST).union(L_FIRST.join(L_PREFIX.closure()).product(LOOP));

	/** The original temporal formula. */
	private final Formula formula;
	/** The original variable bounds. */
	public final PardinusBounds bounds;
	/** The past operator depth. */
	public final int past_depth;
	/** Map logging the translation of temporal formulas, from resulting formula to original one. **/
	public final Map<Formula,Formula> tempTransLog = new HashMap<Formula,Formula>();
	
	/**
	 * Constructs a new temporal translator to expand temporal formulas and variable
	 * bounds.
	 * 
	 * @param form
	 *            the original temporal formula.
	 * @param bnds
	 *            the original variable bounds.
	 */
	public TemporalTranslator(Formula formula, PardinusBounds bounds, Options options) {
		bounds = bounds.clone();
		
		// [HASLab] if not decomposed, use the amalgamated if any
		if (!options.decomposed() && bounds.amalgamated!=null)
			bounds = bounds.amalgamated();
		
		// [HASLab] retrieve the additional formula imposed by the symbolic
		// bounds, depending on execution stage
		Formula symbForm = Formula.TRUE;
		// [HASLab] if decomposed mode, the amalgamated bounds are always considered
		if (options.decomposed() && bounds.amalgamated() != null)
			symbForm = bounds.amalgamated().resolve(options.reporter());
		// [HASLab] then use regular bounds
		symbForm = symbForm.and(bounds.resolve(options.reporter()));

		formula = formula.and(symbForm);
		
		this.formula = formula;
		this.bounds = bounds;
		this.past_depth = countHeight(formula);
	}

	/**
	 * Translates {@link PardinusBounds temporal bound} into standard bounds by
	 * expanding the bound trace over {@link kodkod.ast.VarRelation variable
	 * relations} by appending the {@link #STATE state sig} to the bound. The bounds
	 * of static relations should remain unchanged. The size of the bounds depends
	 * on the trace length passed. Unrolls must be applied if there are past
	 * operators. If the formula contains "always" operator, the bounds can be
	 * optimized.
	 * 
	 * @see TemporalBoundsExpander
	 * 
	 * @param traceLength
	 *            the current trace length.
	 * @return the temporal bounds expanded into standard bounds.
	 */
	public PardinusBounds expand(int traceLength) {
		return TemporalBoundsExpander.expand(bounds, traceLength, past_depth);
	}

	/**
	 * Converts an LTL temporal formula into its FOL static representation. The
	 * formula is previously converted into negative normal form (NNF) to guarantee
	 * the correct translation of the temporal operators. The
	 * {@link kodkod.ast.VarRelation variable relations} contain themselves their
	 * representation into the expanded static shape. If there are no past operators
	 * or there are "always" operators, the translation can be simplified.
	 * 
	 * @see LTL2FOLTranslator
	 * 
	 * @return the static version of the temporal formula.
	 */
	public Formula translate() {
		tempTransLog.clear();
		return LTL2FOLTranslator.translate(formula, 0, past_depth > 1, tempTransLog);
	}

	/**
	 * Checks whether an AST node has temporal constructs, i.e., occurrences of
	 * {@link kodkod.ast.operator.TemporalOperator temporal operations} or
	 * {@link kodkod.ast.VarRelation variable relations}.
	 * 
	 * @param node
	 *            the node to be checked.
	 * @return whether the node has temporal constructs.
	 */
	public static boolean isTemporal(Node node) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			@Override
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}

			@Override
			public Boolean visit(Relation relation) {
				return cache(relation, relation.isVariable());
			}
		};
		return (boolean) node.accept(det);
	}
	
	public static boolean hasTemporalOps(Node node) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			@Override
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}
			
		};
		return (boolean) node.accept(det);
	}

	/** Count the depth of past operators of the given AST tree. */
	public static int countHeight(Node node) {
		ReturnVisitor<Integer, Integer, Integer, Integer> vis = new ReturnVisitor<Integer, Integer, Integer, Integer>() {
			private int max(int a, int b) {
				return (a >= b) ? a : b;
			}

			private int max(int a, int b, int c) {
				return (a >= b) ? (a >= c ? a : c) : (b >= c ? b : c);
			}

			public Integer visit(Relation x) {
				return 0;
			}

			public Integer visit(IntConstant x) {
				return 0;
			}

			public Integer visit(ConstantFormula x) {
				return 0;
			}

			public Integer visit(Variable x) {
				return 0;
			}

			public Integer visit(ConstantExpression x) {
				return 0;
			}

			public Integer visit(NotFormula x) {
				return x.formula().accept(this);
			}

			public Integer visit(UnaryTempFormula x) {
				int n = 0;
				if (x.op().equals(TemporalOperator.ONCE) || x.op().equals(TemporalOperator.HISTORICALLY)
						|| x.op().equals(TemporalOperator.BEFORE))
					n = 1;
				int l = x.formula().accept(this);
				return n + l;
			} // [HASLab] temporal nodes

			public Integer visit(IntToExprCast x) {
				return x.intExpr().accept(this);
			}

			public Integer visit(Decl x) {
				return x.expression().accept(this);
			}

			public Integer visit(ExprToIntCast x) {
				return x.expression().accept(this);
			}

			public Integer visit(UnaryExpression x) {
				return x.expression().accept(this);
			}

			public Integer visit(TempExpression x) {
				return x.expression().accept(this);
			} // [HASLab] temporal nodes

			public Integer visit(UnaryIntExpression x) {
				return x.intExpr().accept(this);
			}

			public Integer visit(MultiplicityFormula x) {
				return x.expression().accept(this);
			}

			public Integer visit(BinaryExpression x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(ComparisonFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(BinaryFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(BinaryTempFormula x) {
				int n = 0;
				if (x.op().equals(TemporalOperator.SINCE) || x.op().equals(TemporalOperator.TRIGGERED))
					n = 1;
				int l = max(x.left().accept(this), x.right().accept(this));
				return n + l;
			} // [HASLab] temporal nodes

			public Integer visit(BinaryIntExpression x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(IntComparisonFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(IfExpression x) {
				return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
			}

			public Integer visit(IfIntExpression x) {
				return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
			}

			public Integer visit(SumExpression x) {
				return max(x.decls().accept(this), x.intExpr().accept(this));
			}

			public Integer visit(QuantifiedFormula x) {
				return max(x.decls().accept(this), x.formula().accept(this));
			}

			public Integer visit(Comprehension x) {
				return max(x.decls().accept(this), x.formula().accept(this));
			}

			public Integer visit(Decls x) {
				int max = 0, n = x.size();
				for (int i = 0; i < n; i++)
					max = max(max, x.get(i).accept(this));
				return max;
			}

			public Integer visit(ProjectExpression x) {
				int max = x.expression().accept(this);
				for (Iterator<IntExpression> t = x.columns(); t.hasNext();) {
					max = max(max, t.next().accept(this));
				}
				return max;
			}

			public Integer visit(RelationPredicate x) {
				if (x instanceof Function) {
					Function f = ((Function) x);
					return max(f.domain().accept(this), f.range().accept(this));
				}
				return 0;
			}

			public Integer visit(NaryExpression x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}

			public Integer visit(NaryIntExpression x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}

			public Integer visit(NaryFormula x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}
		};
		Object ans = node.accept(vis);
		if (ans instanceof Integer)
			return ((Integer) ans).intValue() + 1;
		else
			return 1;
	}

//	/** Tests whether an always operator occurs in the given AST tree. */
//	private static boolean hasAlways(Node node) {
//		final AbstractDetector detector = new AbstractDetector(Collections.emptySet()) {
//			public Boolean visit(UnaryTempFormula form) {
//				if (form.op() == TemporalOperator.ALWAYS)
//					return cache(form, Boolean.TRUE);
//				return super.visit(form);
//			}
//		};
//		return (Boolean) node.accept(detector);
//	}
	
	/** Interprets the step of a state tuple from its name. */
	public static int interpretState(Tuple tuple) {
		String label = tuple.atom(0).toString();
		String[] labelS = label.split(STATE_SEP);
		return Integer.valueOf(labelS[0].substring(4)); 
	}

	/** Interprets the unrolled step of a state tuple from its name. */
	public static int interpretUnroll(Tuple tuple) {
		String label = tuple.atom(0).toString();
		String[] labelS = label.split(STATE_SEP);
		return Integer.valueOf(labelS[1])+1; 
	}

}
