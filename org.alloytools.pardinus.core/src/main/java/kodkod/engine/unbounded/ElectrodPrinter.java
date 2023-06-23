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
package kodkod.engine.unbounded;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

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
import kodkod.ast.LeafExpression;
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
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.engine.InvalidSolverParamException;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.Translation.Whole;
import kodkod.engine.ltl2fol.InvalidMutableExpressionException;
import kodkod.engine.fol2sat.Translator;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.SparseSequence;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Translates an unbounded temporal model finding problem into an Electrod
 * problem in its concrete syntax. This includes the universe, bounds of the
 * variables, the goal as a relational formula and the symmetry breaking
 * predicate.
 * 
 * Electrod has currently limited support for integers. Although integer
 * operations and formulas over integers are supported, the conversion between
 * integer atoms and their numeric semantics is not.
 * 
 * @author Nuno Macedo // [HASLab] unbounded temporal model finding
 */
public class ElectrodPrinter {

	/**
	 * Translates and prints an unbounded temporal model finding problem into
	 * Electrod. Intercepts the symmetry breaking predicate so that it can be
	 * used by Electrod.
	 * 
	 * @param formula
	 *            the problem's formula.
	 * @param bounds
	 *            the problem's bounds.
	 * @param rep 
	 * @return the printed Electrod problem.
	 * @throws InvalidUnboundedProblem
	 *             if the problem is not supported by Electrod.
	 */
	public static String print(Formula formula, PardinusBounds bounds, Reporter rep)
			throws InvalidUnboundedProblem {
		// use a reporter to intercept the symmetry breaking predicate
		Options opt = new ExtendedOptions();
		StringBuilder temp = new StringBuilder();
		Reporter reporter = new AbstractReporter() {
			
			@Override
			public void warning(String warning) {
				rep.warning(warning);
			}
			
			@Override
			public void reportLex(List<Entry<Relation, Tuple>> _original,
					List<Entry<Relation, Tuple>> _permuted) {
				if (_original.size()+_permuted.size()==0)
					return;
				String tmp = printLexList(_original);
				temp.append(tmp.substring(0,tmp.length()-1));
				temp.append(" <= ");
				temp.append(printLexList(_permuted).substring(1));
				temp.append(";\n");
			}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				rep.detectedSymmetries(parts);
			}
			
			@Override
			public void debug(String debug) {
				rep.debug(debug);
			}

		};
		opt.setReporter(reporter);
		
//		Map<Name, Set<RelationPredicate>> preds = AnnotatedNode.annotate(formula).predicates();
//		for (RelationPredicate pred : preds.get(Name.FUNCTION)) {
//			RelationPredicate.Function func = (RelationPredicate.Function) pred;
//			Expression upp = bounds.upperSymbBounds(func.relation());
//			if (upp != null && upp instanceof BinaryExpression && ((BinaryExpression) upp).op().equals(ExprOperator.PRODUCT) && 
//					((BinaryExpression) upp).left().equals(func.domain()) && ((BinaryExpression) upp).right().equals(func.range()))
//				System.out.println(func.relation() + " : " + func.domain() +" -> "+func.targetMult()+" "+func.range());
//		}
		

		// retrieve the additional formula imposed by the symbolic
		// bounds, depending on execution stage
		Formula symbForm = Formula.TRUE;
		// if decomposed mode, the amalgamated bounds are always considered
		if (opt.decomposed() && bounds.amalgamated() != null)
			symbForm = bounds.amalgamated().resolve(opt.reporter());
		// otherwise use regular bounds
		else
			symbForm = bounds.resolve(opt.reporter());
		// NOTE: this is already being performed inside the translator, but is not accessible

		Whole t = Translator.translate(formula.and(symbForm), bounds, opt);
		bounds = (PardinusBounds) t.bounds();

		StringBuilder sb = new StringBuilder();
		sb.append(printUniverse(bounds.universe()));
		sb.append(printBounds(bounds));
		sb.append(printSymmetries(temp.toString()));
		sb.append(printConstraint(formula.and(symbForm)));
		return sb.toString();
	}

	/**
	 * Print the universe of atoms.
	 * 
	 * @param universe the universe of atoms.
	 * @return the universe in Electrod's concrete syntax.
	 */
	private static String printUniverse(Universe universe) {
		StringBuilder sb = new StringBuilder("univ : { ");
		Iterator<Object> it = universe.iterator();
		while (it.hasNext()) {
			sb.append(normRel(it.next().toString()));
			sb.append(" ");
		}
		sb.append("};\n\n");
		return sb.toString();
	}

	/**
	 * Prints the goal formula, either a run or check command. At the Kodkod
	 * level, every thing is a run command (checks are simply negated goals).
	 * 
	 * @param formula
	 *            the goal formula.
	 * @return the goal in Electrod's concrete syntax.
	 */
	private static String printConstraint(Formula formula) {
		StringBuilder sb = new StringBuilder("run\n");
		if (formula instanceof NaryFormula && ((NaryFormula) formula).op() == FormulaOperator.AND) {
			for (int i = 0; i < ((NaryFormula) formula).size(); i++) {
				sb.append(printFormula(((NaryFormula) formula).child(i)));
				sb.append(";\n");
			}
		} else {
			sb.append(printFormula(formula));
			sb.append(";\n");
		}
		return sb.toString();
	}

	/**
	 * Prints the symmetries of the problem, or nothing if no symmetries were
	 * found, since this block is optional.
	 * 
	 * @param syms
	 *            the symmetries.
	 * @return the symmetries in Electrod's concrete syntax or empty.
	 */
	private static String printSymmetries(String syms) {
		if (syms.length() == 0)
			return syms;
		StringBuilder sb = new StringBuilder("sym\n");
		sb.append(normRel(syms));
		sb.append("\n");
		return sb.toString();
	}

	/**
	 * Prints the bounds of the declared relations, distinguishing between
	 * static and variable relations.
	 * 
	 * @param bounds
	 *            the bounds.
	 * @return the bounds in Electrod's concrete syntax.
	 */
	private static String printBounds(Bounds bounds) {
		StringBuilder sb = new StringBuilder();
		Bounds bnd = bounds;
		for (Relation r : bnd.relations()) {
			if (r.isVariable())
				sb.append("var ");
			else
				sb.append("const ");
			sb.append(normRel(r.toString()));
			sb.append(" :");
			sb.append(r.arity());
			sb.append(" ");
			if (bnd.lowerBound(r).size() == bnd.upperBound(r).size()) {
				sb.append(printTupleList(bnd.lowerBound(r)));
			}
			else {
				sb.append(printTupleList(bnd.lowerBound(r)));
				sb.append(" ");
				sb.append(printTupleList(bnd.upperBound(r)));
			}
			sb.append(";\n");
		}
		sb.append("const ints :1 ");
		sb.append(printIntList(bnd.intBounds()));
		sb.append(";\n\n");
		return sb.toString();
	}

	/**
	 * Prints a tuple list.
	 * 
	 * @param tuples
	 *            the tuple list.
	 * @return the tuple list in Electrod's concrete syntax.
	 */
	private static String printTupleList(Collection<Tuple> tuples) {
		StringBuilder sb = new StringBuilder("{ ");
		for (Tuple t : tuples) {
			sb.append("(");
			sb.append(printTuple(t));
			sb.append(") ");
		}
		sb.append("}");
		return sb.toString();
	}
	
	/**
	 * Prints the integer list of atoms.
	 * 
	 * @param ints the integer list.
	 * @return the integer list in Electrod's concrete syntax.
	 */
	private static Object printIntList(SparseSequence<TupleSet> ints) {
		StringBuilder sb = new StringBuilder("{ ");
		Iterator<IndexedEntry<TupleSet>> it = ints.iterator();
		while (it.hasNext()) {
			sb.append("(");
			sb.append(printTuple(it.next().value().iterator().next()));
			sb.append(") ");
		}
		sb.append("}");
		return sb.toString();
	}
	
	/**
	 * Prints the detected symmetries.
	 * 
	 * @param syms
	 *            the detected symmetries.
	 * @return the symmetries in Electrod's concrete syntax.
	 */
	private static String printLexList(List<Entry<Relation, Tuple>> syms) {
		StringBuilder sb = new StringBuilder("");
		sb.append("[ ");
		for (Entry<Relation, Tuple> t : syms) {
			sb.append("( "); 
			sb.append(t.getKey());
			sb.append(printTuple(t.getValue()));
			sb.append(") ");
		}
		sb.append("] ");
		return sb.toString().substring(0,sb.length()-1);
	}
	
	
	/**
	 * Prints a tuple.
	 * 
	 * @param tuple
	 *            the tuple.
	 * @return the tuple in Electrod's concrete syntax.
	 */
	private static String printTuple(Tuple tuple) {
		StringBuilder sb = new StringBuilder(" ");
		for (int i = 0; i < tuple.arity(); i++) {
			sb.append(normRel(tuple.atom(i).toString()));
			sb.append(" ");
		}
		return sb.toString();
	}
	
	/**
	 * Prints a formula.
	 * 
	 * @param formula
	 *            the formula.
	 * @return the formula in Electrod's concrete syntax.
	 */
	private static String printFormula(Formula formula) {
		final LTL2Electrod formatter = new LTL2Electrod(0,80);
		formula.accept(formatter);
		return formatter.tokens.toString();
	
	}

	/**
	 * Prints a temporal formula into Electrod's concrete representation.
	 * Adapted from Kodkod's {@link PrettyPrinter pretty printer}. Main change
	 * is breaking the top level conjuncts into clauses.
	 */
	private static class LTL2Electrod implements VoidVisitor {
			final StringBuilder tokens;
			private final int lineLength;
			private int indent, lineStart;
			private Formula lastFormula;
			
			/**
			 * Constructs a new tokenizer.
			 * @ensures no this.tokens
			 */
			LTL2Electrod(int offset, int line) {
				assert offset >= 0 && offset < line;
				this.tokens = new StringBuilder();
				this.lineLength = line;
				this.lineStart = 0;
				this.indent = offset;
				indent();
			}
			
			/*--------------FORMATTERS---------------*/
				
			/** @ensures this.tokens' = concat [ this.tokens, " ", token, " " ]*/
			private void infix(Object token) { 
				space();
				tokens.append(token);
				space();
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, token, " " ]*/
			private void keyword(Object token) { 
				append(token);
				space();
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, ", " ]*/
			private void comma() { 
				tokens.append(","); 
				space(); 
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, ": " ]*/
			private void colon() { 
				tokens.append(":"); 
				space(); 
			}
			
			/** @ensures adds this.indent spaces to this.tokens */
			private void indent() { for(int i = 0; i < indent; i++) { space(); } }
			
			/** @ensures adds newline plus this.indent spaces to this.tokens */
			private void newline() { 
				tokens.append("\n");
				lineStart = tokens.length();
				indent();
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  " " ] **/
			private void space() { tokens.append(" "); }
		
			/** @ensures this.tokens' = concat [ this.tokens, token ]*/
			private void append(Object token) { 
				final String str = String.valueOf(token);
				if ((tokens.length() - lineStart + str.length()) > lineLength) {
					newline();
				}
				tokens.append(str);
			}
			
			/*--------------LEAVES---------------*/
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(Relation node) { 
				String s = String.valueOf(node);
				append(normRel(s)); 
			}

			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(Variable node) { append(normRel(node.name())); }

			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(ConstantExpression node) { append(node); }
			
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(IntConstant node) {
				append(node); 
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(ConstantFormula node) { append(node); }
			
			/*--------------DECLARATIONS---------------*/
			/** 
			 * @ensures this.tokens' = 
			 *   concat[ this.tokens, tokenize[ node.variable ], ":", tokenize[ node.expression ] 
			 **/
			public void visit(Decl node) {
				node.variable().accept(this);
				colon();
				if (node.multiplicity()!=Multiplicity.ONE) {
					append(node.multiplicity());
					space();
				}
				node.expression().accept(this);
			}
			
			/** 
			 * @ensures this.tokens' = 
			 *   concat[ this.tokens, tokenize[ node.declarations[0] ], ",", 
			 *    ..., tokenize[ node.declarations[ node.size() - 1 ] ] ] 
			 **/
			public void visit(Decls node) {
				Iterator<Decl> decls = node.iterator();
				decls.next().accept(this);
				while(decls.hasNext()) { 
					comma();
					decls.next().accept(this);
				}
			}
			
			/*--------------UNARY NODES---------------*/
			
			/** @ensures this.tokenize' = 
			 *   (parenthesize => concat [ this.tokens, "(", tokenize[child], ")" ] else 
			 *                    concat [ this.tokens, tokenize[child] ]*/
			private void visitChild(Node child, boolean parenthesize) { 
				if (parenthesize) { append("("); }
				child.accept(this);
				if (parenthesize) { append(")"); }
			}
			
			/** @return true if the given expression should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(Expression child) { 
				// [HASLab] abuse parenthesis
				return !(child instanceof LeafExpression);
			}
			
			/** @return true if the given expression should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(IntExpression child) { 
				// [HASLab] abuse parenthesis
				return true;
			}
			
			/** @return true if the given formula should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(Formula child) { 
				// [HASLab] abuse parenthesis
				return !(child instanceof ConstantFormula);
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			public void visit(UnaryExpression node) { 
				append(node.op());
				visitChild(node.expression(), parenthesize(node.expression()));
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's not an instance of unary int expression or int constant. **/
			public void visit(UnaryIntExpression node)  { 
				final IntExpression child = node.intExpr();
				final IntOperator op = node.op();
				final boolean parens = 
					(op==IntOperator.ABS) || (op==IntOperator.SGN) || 
					parenthesize(child);
				append(node.op());
				visitChild(child, parens);
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's not an instance of not formula, constant formula, or 
			 * relation predicate. **/
			public void visit(NotFormula node) {
				append("!");
				final boolean pchild = parenthesize(node.formula());
				indent += pchild ? 2 : 1;
				visitChild(node.formula(), parenthesize(node.formula()));
				indent -= pchild ? 2 : 1;
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			public void visit(MultiplicityFormula node) {
				keyword(node.multiplicity());
				visitChild(node.expression(), parenthesize(node.expression()));
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			// [HASLab] temporal formulas
			public void visit(UnaryTempFormula node) { 
				keyword(node.op());
				indent++;
				visitChild(node.formula(), parenthesize(node.op(), node.formula()));
				indent--;
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			// [HASLab] temporal formulas
			public void visit(TempExpression node) { 
				visitChild(node.expression(), parenthesize(node.op(), node.expression()));
				keyword(node.op());
			}

			/*--------------BINARY NODES---------------*/
			
			/** @return true if the given  expression needs to be parenthesized if a 
			 * child of a binary  expression with the given operator */
			private boolean parenthesize(ExprOperator op, Expression child) { 
				return child instanceof IfExpression ||
					   child instanceof NaryExpression ||
				       (child instanceof BinaryExpression && 
				        (op==ExprOperator.JOIN || 
				         ((BinaryExpression)child).op()!=op));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(BinaryExpression node) {
				final ExprOperator op = node.op();
				visitChild(node.left(), parenthesize(op, node.left()));
				infix(op);
				visitChild(node.right(), parenthesize(op, node.right()));
			}
			
			/** @return true if the given operator is assocative */
			private boolean associative(IntOperator op) { 
				switch(op) { 
				case DIVIDE : case MODULO : case SHA : case SHL : case SHR : return false;
				default : return true;
				}
			}
			
			/** @return true if the given int expression needs to be parenthesized if a 
			 * child of a binary int expression with the given operator */
			private boolean parenthesize(IntOperator op, IntExpression child) { 
				return child instanceof SumExpression ||
					   child instanceof IfIntExpression || 
					   child instanceof NaryIntExpression ||
				       (child instanceof BinaryIntExpression && 
				        (!associative(op) || ((BinaryIntExpression)child).op()!=op));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(BinaryIntExpression node) {
				final IntOperator op = node.op();
				visitChild(node.left(), parenthesize(op, node.left()));
				infix(op);
				visitChild(node.right(), parenthesize(op, node.right()));
			}
			
			/** @return true if the given formula needs to be parenthesized if a 
			 * child of a binary formula with the given operator */
			private boolean parenthesize(FormulaOperator op, Formula child) { 
				return child instanceof QuantifiedFormula || 
					   //child instanceof NaryFormula ||
				       (child instanceof BinaryFormula && 
				        (op==FormulaOperator.IMPLIES || 
				         ((BinaryFormula)child).op()!=op));
			}

			/** @return true if the given temporal formula needs to be parenthesized, 
			 * assumed to be always */
			// [HASLab] temporal formulas
			private boolean parenthesize(TemporalOperator op, Formula child) { 
				return true;
			}
			
			/** @return true if the given temporal expression needs to be parenthesized, 
			 * assumed to be always */
			// [HASLab] temporal formulas
			private boolean parenthesize(TemporalOperator op, Expression child) { 
				return true;
			}

			/** @ensures appends the tokenization of the given node to this.tokens */
			// [HASLab] break conjuncts if top level
			public void visit(BinaryFormula node) {
				lastFormula = node;
				final FormulaOperator op = node.op();
				final boolean pleft = parenthesize(op, node.left());
				if (pleft) indent++;
				visitChild(node.left(), pleft);
				if (pleft) indent--;
				if (op == FormulaOperator.AND && indent == 0)
					append(";");
				else
					infix(op);
				newline();
				final boolean pright =  parenthesize(op, node.right());
				if (pright) indent++;
				visitChild(node.right(), pright);
				if (pright) indent--;
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op, tokenize[node.right] */
			public void visit(ComparisonFormula node) {
				lastFormula = node;
				visitChild(node.left(), parenthesize(node.left()));
				infix(node.op());
				visitChild(node.right(), parenthesize(node.right()));
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op, tokenize[node.right] */
			public void visit(IntComparisonFormula node) {
				lastFormula = node;
				visitChild(node.left(), parenthesize(node.left()));
				infix(node.op());
				visitChild(node.right(), parenthesize(node.right()));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			// [HASLab] temporal formulas
			public void visit(BinaryTempFormula node) {
				lastFormula = node;
				final TemporalOperator op = node.op();
				final boolean pleft = parenthesize(op, node.left());
				if (pleft) indent++;
				visitChild(node.left(), pleft);
				if (pleft) indent--;
				infix(op);
				newline();
				final boolean pright =  parenthesize(op, node.right());
				if (pright) indent++;
				visitChild(node.right(), pright);
				if (pright) indent--;
			}
			
			/*--------------TERNARY NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(IfExpression node) {
				visitChild(node.condition(), parenthesize(node.condition()));
				infix("=>");
				indent++;
				newline();
				visitChild(node.thenExpr(), parenthesize(node.thenExpr()));
				infix("else");
				newline();
				visitChild(node.elseExpr(), parenthesize(node.elseExpr()));
				indent--;
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(IfIntExpression node) {
				visitChild(node.condition(), parenthesize(node.condition()));
				infix("=>");
				indent++;
				newline();
				visitChild(node.thenExpr(), parenthesize(node.thenExpr()));
				infix("else");
				newline();
				visitChild(node.elseExpr(), parenthesize(node.elseExpr()));
				indent--;
			}
			
			/*--------------VARIABLE CREATOR NODES---------------*/
			/** @ensures this.tokens' = concat[ this.tokens, 
			 *   "{", tokenize[node.decls], "|", tokenize[ node.formula ], "}" ]*/
			public void visit(Comprehension node) {
				append("{");
				node.decls().accept(this);
				infix("{");
				indent++;
				newline();
				node.formula().accept(this);
				indent--;
				newline();
				append("}");
				append("}");	
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  "sum",
			 *   tokenize[node.decls], "|", tokenize[ node.intExpr ],  ]*/
			public void visit(SumExpression node) {
				keyword("sum");
				node.decls().accept(this);
				infix("|");
				node.intExpr().accept(this);
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  node.quantifier,
			 *   tokenize[node.decls], "|", tokenize[ node.formula ] ]*/
			public void visit(QuantifiedFormula node) {
				lastFormula = node;
				keyword(node.quantifier());
				node.decls().accept(this);
				infix("{");
				indent++;
				newline();
				node.formula().accept(this);
				newline();
				indent--;
				append("}");
			}
			
			/*--------------NARY NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(NaryExpression node) {
				final ExprOperator op = node.op();
				visitChild(node.child(0), parenthesize(op, node.child(0)));
				for(int i = 1, size = node.size(); i < size; i++) {
					infix(op);
					visitChild(node.child(i), parenthesize(op, node.child(i)));
				}
			}
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(NaryIntExpression node) {
				final IntOperator op = node.op();
				visitChild(node.child(0), parenthesize(op, node.child(0)));
				for(int i = 1, size = node.size(); i < size; i++) {
					infix(op);
					visitChild(node.child(i), parenthesize(op, node.child(i)));
				}
			}
			/** @ensures appends the tokenization of the given node to this.tokens */
			// [HASLab] break conjuncts if top level
			public void visit(NaryFormula node) {
				lastFormula = node;
				final FormulaOperator op = node.op();
				boolean parens = parenthesize(op, node.child(0));
				if (parens) indent++;
				visitChild(node.child(0), parens);
				if (parens) indent--;
				for(int i = 1, size = node.size(); i < size; i++) { 
					if (op == FormulaOperator.AND && indent==0)
						append(";");
					else
						infix(op);
					newline();
					parens = parenthesize(op, node.child(i));
					if (parens) indent++;
					visitChild(node.child(i), parens);
					if (parens) indent--;
				}
			}
			/*--------------OTHER NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(ProjectExpression node) {
				if (node.arity() > 1)
					throw new IllegalArgumentException("No support for projections: "+node);
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, "Int","[",
			 *   tokenize[node.intExpr], "]" ] **/
			// [HASLab] integer relations
			public void visit(IntToExprCast node) {
				throw new InvalidUnboundedProblem(lastFormula);
//				append("Int");
//				append("[");
//				node.intExpr().accept(this);
//				append("]");
			}
			
			/** @throws InvalidUnboundedProblem 
			 * @ensures this.tokens' = concat[ this.tokens, "int","[",
			 *   tokenize[node.expression], "]" ] **/
			// [HASLab] integer relations
			public void visit(ExprToIntCast node) {
				switch(node.op()) { 
				case SUM:
					throw new InvalidUnboundedProblem(lastFormula);
//					append("int");
//					append("[");
//					node.expression().accept(this);
//					append("]");
//					break;
				case CARDINALITY : 
					append("#");
					append("(");
					node.expression().accept(this);
					append(")");
					break;
				default : throw new IllegalArgumentException("unknown operator: " + node.op());
				}
				
			}

			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(RelationPredicate node) {
				lastFormula = node;
				switch(node.name()) { 
				case ACYCLIC : 
					append("acyclic");
					append("[");
					node.relation().accept(this);
					append("]");
					break;
				case FUNCTION : 
					visit((BinaryFormula) node.toConstraints());
					break;
				case TOTAL_ORDERING : 
					visit((NaryFormula) node.toConstraints());
					break;
				default:
					throw new AssertionError("unreachable");
				}
				
			}
			
		}

	static private final String[] protected_keywords = { "run", "expect", "sat", "unsat", "invariant", "true", "false",
			"after", "always", "eventually", "until", "releases", "before", "historically", "once", "since",
			"triggered", "all", "some", "one", "no", "lone", "let", "disj", "iff", "implies", "then", "else", "or",
			"and", "in", "inst", "sym", "not", "var", "const", "univ", "iden", "none"

	};

	/**
	 * Converts identifiers into a version that is compatible with Electrod by
	 * removing '/', '.' and '$' symbols.
	 * 
	 * TODO: what if id already has # symbols?
	 * 
	 * @param id the identifier.
	 * @return the normalized identifier.
	 */
	static String normRel(String id) {
		if (id.isEmpty())
			return "unnamed#unnamed";
		else if (Arrays.asList(protected_keywords).contains(id))
			id = "p#" + id;
		return id.replace("/", "##").replace(".", "#").replace("$", "skolem#");
	}

	/**
	 * Converts identifiers that are compatible with Electrod back to their Kodkod
	 * internal representation.
	 * 
	 * * TODO: what if id already has # symbols?
	 * 
	 * @param id the identifier.
	 * @return the denormalized identifier.
	 */
	static String denormRel(String id) {
		if (id.equals("unnamed#unnamed"))
			return "";
		return id.replace("p#", "").replace("skolem#", "$").replace("##", "/").replace("#", ".");
	}

}

