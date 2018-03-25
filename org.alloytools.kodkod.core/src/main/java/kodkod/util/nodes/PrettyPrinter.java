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
package kodkod.util.nodes;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.FixFormula;
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
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.VoidVisitor;

/**
 * Pretty-prints Kodkod nodes.
 *
 * @author Emina Torlak
 */
public final class PrettyPrinter {

    /**
     * Returns a dot representation of the given node that can be visualized with
     * GraphViz.
     *
     * @return a dot representation of the given node that can be visualized with
     *         GraphViz.
     */
    public static String dotify(Node node) {
        return Dotifier.apply(node);
    }

    /**
     * Returns a pretty-printed string representation of the given node, with each
     * line offset by at least the given number of whitespaces. The line parameter
     * determines the length of each pretty-printed line, including the offset.
     *
     * @requires 0 <= offset < line
     * @return a pretty-printed string representation of the given node
     */
    public static String print(Node node, int offset, int line) {
        final Formatter formatter = new Formatter(offset, line);
        node.accept(formatter);
        return formatter.tokens.toString();
    }

    /**
     * Returns a pretty-printed string representation of the given node, with each
     * line offset by at least the given number of whitespaces.
     *
     * @requires 0 <= offset < 80
     * @return a pretty-printed string representation of the given node
     */
    public static String print(Node node, int offset) {
        return print(node, offset, 80);
    }

    /**
     * Returns a pretty-printed string representation of the given formulas, with
     * each line offset by at least the given number of whitespaces.
     *
     * @requires 0 <= offset < 80
     * @return a pretty-printed string representation of the given formulas
     */
    public static String print(Set<Formula> formulas, int offset) {
        return print(formulas, offset, 80);
    }

    /**
     * Returns a pretty-printed string representation of the given formulas, with
     * each line offset by at least the given number of whitespaces. The line
     * parameter determines the length of each pretty-printed line, including the
     * offset.
     *
     * @requires 0 <= offset < line
     * @return a pretty-printed string representation of the given formulas
     */
    public static String print(Set<Formula> formulas, int offset, int line) {
        final Formatter formatter = new Formatter(offset, line);
        for (Formula f : formulas) {
            f.accept(formatter);
            formatter.newline();
        }
        return formatter.tokens.toString();
    }

    /**
     * Generates a buffer of tokens comprising the string representation of a given
     * node. The buffer contains at least the parentheses needed to correctly
     * represent the node's tree structure.
     *
     * @specfield tokens: seq<Object>
     * @author Emina Torlak
     */
    private static class Formatter implements VoidVisitor {

        final StringBuilder tokens;
        // final int offset;
        private final int   lineLength;
        private int         indent, lineStart;

        /**
         * Constructs a new tokenizer.
         *
         * @ensures no this.tokens
         */
        Formatter(int offset, int line) {
            assert offset >= 0 && offset < line;
            this.tokens = new StringBuilder();
            // this.offset = offset;
            this.lineLength = line;
            this.lineStart = 0;
            this.indent = offset;
            indent();
        }

        /*--------------FORMATTERS---------------*/

        /**
         * @ensures this.tokens' = concat [ this.tokens, " ", token, " " ]
         */
        private void infix(Object token) {
            space();
            tokens.append(token);
            space();
        }

        /**
         * @ensures this.tokens' = concat [ this.tokens, token, " " ]
         */
        private void keyword(Object token) {
            append(token);
            space();
        }

        /** @ensures this.tokens' = concat [ this.tokens, ", " ] */
        private void comma() {
            tokens.append(",");
            space();
        }

        /** @ensures this.tokens' = concat [ this.tokens, ": " ] */
        private void colon() {
            tokens.append(":");
            space();
        }

        /** @ensures adds this.indent spaces to this.tokens */
        private void indent() {
            for (int i = 0; i < indent; i++) {
                space();
            }
        }

        /**
         * @ensures adds newline plus this.indent spaces to this.tokens
         */
        private void newline() {
            tokens.append("\n");
            lineStart = tokens.length();
            indent();
        }

        /** @ensures this.tokens' = concat[ this.tokens, " " ] **/
        private void space() {
            tokens.append(" ");
        }

        /** @ensures this.tokens' = concat [ this.tokens, token ] */
        private void append(Object token) {
            final String str = String.valueOf(token);
            if ((tokens.length() - lineStart + str.length()) > lineLength) {
                newline();
            }
            tokens.append(str);
        }

        /*--------------LEAVES---------------*/
        /** @ensures this.tokens' = concat[ this.tokens, node ] */
        @Override
        public void visit(Relation node) {
            append(node);
        }

        /** @ensures this.tokens' = concat[ this.tokens, node ] */
        @Override
        public void visit(Variable node) {
            append(node);
        }

        /** @ensures this.tokens' = concat[ this.tokens, node ] */
        @Override
        public void visit(ConstantExpression node) {
            append(node);
        }

        /** @ensures this.tokens' = concat[ this.tokens, node ] */
        @Override
        public void visit(IntConstant node) {
            append(node);
        }

        /** @ensures this.tokens' = concat[ this.tokens, node ] */
        @Override
        public void visit(ConstantFormula node) {
            append(node);
        }

        /*--------------DECLARATIONS---------------*/
        /**
         * @ensures this.tokens' = concat[ this.tokens, tokenize[ node.variable ], ":",
         *          tokenize[ node.expression ]
         **/
        @Override
        public void visit(Decl node) {
            node.variable().accept(this);
            colon();
            if (node.multiplicity() != Multiplicity.ONE) {
                append(node.multiplicity());
                space();
            }
            node.expression().accept(this);
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, tokenize[ node.declarations[0]
         *          ], ",", ..., tokenize[ node.declarations[ node.size() - 1 ] ] ]
         **/
        @Override
        public void visit(Decls node) {
            Iterator<Decl> decls = node.iterator();
            decls.next().accept(this);
            while (decls.hasNext()) {
                comma();
                decls.next().accept(this);
            }
        }

        /*--------------UNARY NODES---------------*/

        /**
         * @ensures this.tokenize' = (parenthesize => concat [ this.tokens, "(",
         *          tokenize[child], ")" ] else concat [ this.tokens, tokenize[child] ]
         */
        private void visitChild(Node child, boolean parenthesize) {
            if (parenthesize) {
                append("(");
            }
            child.accept(this);
            if (parenthesize) {
                append(")");
            }
        }

        /**
         * @return true if the given expression should be parenthesized when a child of
         *         a compound parent
         */
        private boolean parenthesize(Expression child) {
            return child instanceof BinaryExpression || child instanceof IfExpression;
        }

        /**
         * @return true if the given expression should be parenthesized when a child of
         *         a compound parent
         */
        private boolean parenthesize(IntExpression child) {
            return !(child instanceof UnaryIntExpression || child instanceof IntConstant || child instanceof ExprToIntCast);
        }

        /**
         * @return true if the given formula should be parenthesized when a child of a
         *         compound parent
         */
        private boolean parenthesize(Formula child) {
            return !(child instanceof NotFormula || child instanceof ConstantFormula || child instanceof RelationPredicate);
        }

        /**
         * @ensures appends the given op and child to this.tokens; the child is
         *          parenthesized if it's an instance of binary expression or an if
         *          expression.
         **/
        @Override
        public void visit(UnaryExpression node) {
            append(node.op());
            visitChild(node.expression(), parenthesize(node.expression()));
        }

        /**
         * @ensures appends the given op and child to this.tokens; the child is
         *          parenthesized if it's not an instance of unary int expression or int
         *          constant.
         **/
        @Override
        public void visit(UnaryIntExpression node) {
            final IntExpression child = node.intExpr();
            final IntOperator op = node.op();
            final boolean parens = (op == IntOperator.ABS) || (op == IntOperator.SGN) || parenthesize(child);
            append(node.op());
            visitChild(child, parens);
        }

        /**
         * @ensures appends the given op and child to this.tokens; the child is
         *          parenthesized if it's not an instance of not formula, constant
         *          formula, or relation predicate.
         **/
        @Override
        public void visit(NotFormula node) {
            append("!");
            final boolean pchild = parenthesize(node.formula());
            indent += pchild ? 2 : 1;
            visitChild(node.formula(), parenthesize(node.formula()));
            indent -= pchild ? 2 : 1;
        }

        /**
         * @ensures appends the given op and child to this.tokens; the child is
         *          parenthesized if it's an instance of binary expression or an if
         *          expression.
         **/
        @Override
        public void visit(MultiplicityFormula node) {
            keyword(node.multiplicity());
            visitChild(node.expression(), parenthesize(node.expression()));
        }

        /*--------------BINARY NODES---------------*/

        /**
         * @return true if the given expression needs to be parenthesized if a child of
         *         a binary expression with the given operator
         */
        private boolean parenthesize(ExprOperator op, Expression child) {
            return child instanceof IfExpression || child instanceof NaryExpression || (child instanceof BinaryExpression && (op == ExprOperator.JOIN || ((BinaryExpression) child).op() != op));
        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(BinaryExpression node) {
            final ExprOperator op = node.op();
            visitChild(node.left(), parenthesize(op, node.left()));
            infix(op);
            visitChild(node.right(), parenthesize(op, node.right()));
        }

        /** @return true if the given operator is assocative */
        private boolean associative(IntOperator op) {
            switch (op) {
                case DIVIDE :
                case MODULO :
                case SHA :
                case SHL :
                case SHR :
                    return false;
                default :
                    return true;
            }
        }

        /**
         * @return true if the given int expression needs to be parenthesized if a child
         *         of a binary int expression with the given operator
         */
        private boolean parenthesize(IntOperator op, IntExpression child) {
            return child instanceof SumExpression || child instanceof IfIntExpression || child instanceof NaryIntExpression || (child instanceof BinaryIntExpression && (!associative(op) || ((BinaryIntExpression) child).op() != op));
        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(BinaryIntExpression node) {
            final IntOperator op = node.op();
            visitChild(node.left(), parenthesize(op, node.left()));
            infix(op);
            visitChild(node.right(), parenthesize(op, node.right()));
        }

        /**
         * @return true if the given formula needs to be parenthesized if a child of a
         *         binary formula with the given operator
         */
        private boolean parenthesize(FormulaOperator op, Formula child) {
            return child instanceof QuantifiedFormula ||
            // child instanceof NaryFormula ||
                   (child instanceof BinaryFormula && (op == FormulaOperator.IMPLIES || ((BinaryFormula) child).op() != op));
        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(BinaryFormula node) {
            final FormulaOperator op = node.op();
            final boolean pleft = parenthesize(op, node.left());
            if (pleft)
                indent++;
            visitChild(node.left(), pleft);
            if (pleft)
                indent--;
            infix(op);
            newline();
            final boolean pright = parenthesize(op, node.right());
            if (pright)
                indent++;
            visitChild(node.right(), pright);
            if (pright)
                indent--;
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op,
         *          tokenize[node.right]
         */
        @Override
        public void visit(ComparisonFormula node) {
            visitChild(node.left(), parenthesize(node.left()));
            infix(node.op());
            visitChild(node.right(), parenthesize(node.right()));
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op,
         *          tokenize[node.right]
         */
        @Override
        public void visit(IntComparisonFormula node) {
            visitChild(node.left(), parenthesize(node.left()));
            infix(node.op());
            visitChild(node.right(), parenthesize(node.right()));
        }

        /*--------------TERNARY NODES---------------*/

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
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

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
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
        /**
         * @ensures this.tokens' = concat[ this.tokens, "{", tokenize[node.decls], "|",
         *          tokenize[ node.formula ], "}" ]
         */
        @Override
        public void visit(Comprehension node) {
            append("{");
            node.decls().accept(this);
            infix("|");
            node.formula().accept(this);
            append("}");
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, "sum", tokenize[node.decls],
         *          "|", tokenize[ node.intExpr ], ]
         */
        @Override
        public void visit(SumExpression node) {
            keyword("sum");
            node.decls().accept(this);
            infix("|");
            node.intExpr().accept(this);
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, node.quantifier,
         *          tokenize[node.decls], "|", tokenize[ node.formula ] ]
         */
        @Override
        public void visit(QuantifiedFormula node) {
            keyword(node.quantifier());
            node.decls().accept(this);
            if (node.domain() != Formula.TRUE) {
                infix("| domain{");
                indent++;
                newline();
                node.domain().accept(this);
                indent--;
                newline();
                infix("}");
                infix("| body{");
                indent++;
                newline();
                node.body().accept(this);
                indent--;
                newline();
                infix("}");
            } else {
                infix("|");
                indent++;
                newline();
                node.body().accept(this);
                indent--;
            }
        }

        @Override
        public void visit(FixFormula node) {
            keyword("fix {");
            newline();
            indent++;
            node.formula().accept(this);
            newline();
            indent--;
            append("} until {");
            newline();
            indent++;
            node.condition().accept(this);
            newline();
            indent--;
            append("}");
        }

        /*--------------NARY NODES---------------*/

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(NaryExpression node) {
            final ExprOperator op = node.op();
            visitChild(node.child(0), parenthesize(op, node.child(0)));
            for (int i = 1, size = node.size(); i < size; i++) {
                infix(op);
                visitChild(node.child(i), parenthesize(op, node.child(i)));
            }
        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(NaryIntExpression node) {
            final IntOperator op = node.op();
            visitChild(node.child(0), parenthesize(op, node.child(0)));
            for (int i = 1, size = node.size(); i < size; i++) {
                infix(op);
                visitChild(node.child(i), parenthesize(op, node.child(i)));
            }
        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(NaryFormula node) {
            final FormulaOperator op = node.op();
            boolean parens = parenthesize(op, node.child(0));
            if (parens)
                indent++;
            visitChild(node.child(0), parens);
            if (parens)
                indent--;
            for (int i = 1, size = node.size(); i < size; i++) {
                infix(op);
                newline();
                parens = parenthesize(op, node.child(i));
                if (parens)
                    indent++;
                visitChild(node.child(i), parens);
                if (parens)
                    indent--;
            }
        }
        /*--------------OTHER NODES---------------*/

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(ProjectExpression node) {
            append("project");
            append("[");
            node.expression().accept(this);
            comma();
            append("<");
            final Iterator<IntExpression> cols = node.columns();
            cols.next().accept(this);
            while (cols.hasNext()) {
                comma();
                cols.next().accept(this);
            }
            append(">");
            append("]");
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, "Int","[",
         *          tokenize[node.intExpr], "]" ]
         **/
        @Override
        public void visit(IntToExprCast node) {
            append("Int");
            append("[");
            node.intExpr().accept(this);
            append("]");
        }

        /**
         * @ensures this.tokens' = concat[ this.tokens, "int","[",
         *          tokenize[node.expression], "]" ]
         **/
        @Override
        public void visit(ExprToIntCast node) {
            switch (node.op()) {
                case SUM :
                    append("int");
                    append("[");
                    node.expression().accept(this);
                    append("]");
                    break;
                case CARDINALITY :
                    append("#");
                    append("(");
                    node.expression().accept(this);
                    append(")");
                    break;
                default :
                    throw new IllegalArgumentException("unknown operator: " + node.op());
            }

        }

        /**
         * @ensures appends the tokenization of the given node to this.tokens
         */
        @Override
        public void visit(RelationPredicate node) {
            switch (node.name()) {
                case ACYCLIC :
                    append("acyclic");
                    append("[");
                    node.relation().accept(this);
                    append("]");
                    break;
                case FUNCTION :
                    RelationPredicate.Function func = (RelationPredicate.Function) node;
                    append("function");
                    append("[");
                    func.relation().accept(this);
                    colon();
                    func.domain().accept(this);
                    infix("->");
                    keyword(func.targetMult());
                    func.range().accept(this);
                    append("]");
                    break;
                case TOTAL_ORDERING :
                    RelationPredicate.TotalOrdering ord = (RelationPredicate.TotalOrdering) node;
                    append("ord");
                    append("[");
                    ord.relation().accept(this);
                    comma();
                    ord.ordered().accept(this);
                    comma();
                    ord.first().accept(this);
                    comma();
                    ord.last().accept(this);
                    append("]");
                    break;
                default :
                    throw new AssertionError("unreachable");
            }

        }

    }

    private static class Dotifier implements VoidVisitor {

        private final StringBuilder     graph = new StringBuilder();
        private final Map<Node,Integer> ids   = new LinkedHashMap<Node,Integer>();

        static String apply(Node node) {
            final Dotifier dot = new Dotifier();
            dot.graph.append("digraph {\n");
            node.accept(dot);
            dot.graph.append("}");
            return dot.graph.toString();
        }

        private boolean visited(Node n) {
            if (ids.containsKey(n))
                return true;
            ids.put(n, ids.size());
            return false;
        }

        private String id(Node n) {
            return "N" + ids.get(n);
        }

        private void node(Node n, String label) {
            graph.append(id(n));
            graph.append("[ label=\"");
            graph.append(ids.get(n));
            graph.append("(");
            graph.append(label);
            graph.append(")\"];\n");
        }

        private void edge(Node n1, Node n2) {
            if (n2 instanceof LeafExpression || n2 instanceof ConstantFormula || n2 instanceof IntConstant) {

            }
            graph.append(id(n1));
            graph.append("->");
            graph.append(id(n2));
            graph.append(";\n");
        }

        private void visit(Node parent, Object label) {
            if (visited(parent))
                return;
            node(parent, label.toString());
        }

        private void visit(Node parent, Object label, Node child) {
            if (visited(parent))
                return;
            node(parent, label.toString());
            child.accept(this);
            edge(parent, child);
        }

        private void visit(Node parent, Object label, Node left, Node right) {
            if (visited(parent))
                return;
            node(parent, label.toString());
            left.accept(this);
            right.accept(this);
            edge(parent, left);
            edge(parent, right);
        }

        private void visit(Node parent, Object label, Node left, Node middle, Node right) {
            if (visited(parent))
                return;
            node(parent, label.toString());
            left.accept(this);
            middle.accept(this);
            right.accept(this);
            edge(parent, left);
            edge(parent, middle);
            edge(parent, right);
        }

        private void visit(Node parent, Object label, Iterator< ? extends Node> children) {
            if (visited(parent))
                return;
            node(parent, label.toString());
            while (children.hasNext()) {
                Node child = children.next();
                child.accept(this);
                edge(parent, child);
            }
        }

        private void visit(Node parent, Object label, Node child, Iterator< ? extends Node> children) {
            if (visited(parent))
                return;
            node(parent, label.toString());
            child.accept(this);
            edge(parent, child);
            while (children.hasNext()) {
                Node other = children.next();
                other.accept(this);
                edge(parent, other);
            }
        }

        @Override
        public void visit(Decls decls) {
            visit(decls, "decls", decls.iterator());
        }

        @Override
        public void visit(Decl decl) {
            visit(decl, "decl", decl.variable(), decl.expression());
        }

        @Override
        public void visit(Relation relation) {
            visit(relation, relation.name());
        }

        @Override
        public void visit(Variable variable) {
            visit(variable, variable.name());
        }

        @Override
        public void visit(ConstantExpression constExpr) {
            visit(constExpr, constExpr.name());
        }

        @Override
        public void visit(NaryExpression expr) {
            visit(expr, expr.op(), expr.iterator());
        }

        @Override
        public void visit(BinaryExpression binExpr) {
            visit(binExpr, binExpr.op(), binExpr.left(), binExpr.right());
        }

        @Override
        public void visit(UnaryExpression unaryExpr) {
            visit(unaryExpr, unaryExpr.op(), unaryExpr.expression());
        }

        @Override
        public void visit(Comprehension comprehension) {
            visit(comprehension, "setcomp", comprehension.decls(), comprehension.formula());
        }

        @Override
        public void visit(IfExpression ifExpr) {
            visit(ifExpr, "ite", ifExpr.condition(), ifExpr.thenExpr(), ifExpr.elseExpr());
        }

        @Override
        public void visit(ProjectExpression project) {
            visit(project, "proj", project.expression(), project.columns());
        }

        @Override
        public void visit(IntToExprCast castExpr) {
            visit(castExpr, castExpr.op(), castExpr.intExpr());
        }

        @Override
        public void visit(IntConstant intConst) {
            visit(intConst, intConst.value());
        }

        @Override
        public void visit(IfIntExpression intExpr) {
            visit(intExpr, "ite", intExpr.condition(), intExpr.thenExpr(), intExpr.elseExpr());
        }

        @Override
        public void visit(ExprToIntCast intExpr) {
            visit(intExpr, intExpr.op(), intExpr.expression());
        }

        @Override
        public void visit(NaryIntExpression intExpr) {
            visit(intExpr, intExpr.op(), intExpr.iterator());
        }

        @Override
        public void visit(BinaryIntExpression intExpr) {
            visit(intExpr, intExpr.op(), intExpr.left(), intExpr.right());
        }

        @Override
        public void visit(UnaryIntExpression intExpr) {
            visit(intExpr, intExpr.op(), intExpr.intExpr());
        }

        @Override
        public void visit(SumExpression intExpr) {
            visit(intExpr, "sum", intExpr.decls(), intExpr.intExpr());
        }

        @Override
        public void visit(IntComparisonFormula intComp) {
            visit(intComp, intComp.op(), intComp.left(), intComp.right());
        }

        @Override
        public void visit(QuantifiedFormula quantFormula) {
            visit(quantFormula, quantFormula.quantifier(), quantFormula.decls(), quantFormula.formula());
        }

        @Override
        public void visit(FixFormula fixFormula) {
            visit(fixFormula, "fix", fixFormula.formula(), fixFormula.condition());
        }

        @Override
        public void visit(NaryFormula formula) {
            visit(formula, formula.op(), formula.iterator());
        }

        @Override
        public void visit(BinaryFormula binFormula) {
            visit(binFormula, binFormula.op(), binFormula.left(), binFormula.right());
        }

        @Override
        public void visit(NotFormula not) {
            visit(not, "not", not.formula());
        }

        @Override
        public void visit(ConstantFormula constant) {
            visit(constant, constant.booleanValue());
        }

        @Override
        public void visit(ComparisonFormula compFormula) {
            visit(compFormula, compFormula.op(), compFormula.left(), compFormula.right());
        }

        @Override
        public void visit(MultiplicityFormula multFormula) {
            visit(multFormula, multFormula.multiplicity(), multFormula.expression());
        }

        @Override
        public void visit(RelationPredicate pred) {
            if (visited(pred))
                return;

            if (pred.name() == RelationPredicate.Name.FUNCTION) {
                final RelationPredicate.Function fp = (RelationPredicate.Function) pred;
                visit(fp, fp.name(), fp.domain(), fp.range());
            } else if (pred.name() == RelationPredicate.Name.TOTAL_ORDERING) {
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) pred;
                visit(tp, tp.name(), tp.ordered(), tp.first(), tp.last());
            } else {
                throw new IllegalArgumentException("Unknown predicate: " + pred);
            }
        }

    }
}
