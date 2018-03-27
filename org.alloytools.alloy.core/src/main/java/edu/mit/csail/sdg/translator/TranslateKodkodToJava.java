/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

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
import kodkod.ast.RelationPredicate.Function;
import kodkod.ast.SumExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.Variable;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Translate a Kodkod formula node to an equivalent Java program that solves the
 * formula.
 * <p>
 * Requirements: atoms must be String objects (since we cannot possibly output a
 * Java source code that can re-generate arbitrary Java objects).
 */

public final class TranslateKodkodToJava implements VoidVisitor {

    /** Count the height of the given Kodkod AST tree. */
    public static int countHeight(Node node) {
        ReturnVisitor<Integer,Integer,Integer,Integer> vis = new ReturnVisitor<Integer,Integer,Integer,Integer>() {

            private int max(int a, int b) {
                return (a >= b) ? a : b;
            }

            private int max(int a, int b, int c) {
                return (a >= b) ? (a >= c ? a : c) : (b >= c ? b : c);
            }

            @Override
            public Integer visit(Relation x) {
                return 1;
            }

            @Override
            public Integer visit(IntConstant x) {
                return 1;
            }

            @Override
            public Integer visit(ConstantFormula x) {
                return 1;
            }

            @Override
            public Integer visit(Variable x) {
                return 1;
            }

            @Override
            public Integer visit(ConstantExpression x) {
                return 1;
            }

            @Override
            public Integer visit(NotFormula x) {
                return 1 + x.formula().accept(this);
            }

            @Override
            public Integer visit(IntToExprCast x) {
                return 1 + x.intExpr().accept(this);
            }

            @Override
            public Integer visit(Decl x) {
                return 1 + x.expression().accept(this);
            }

            @Override
            public Integer visit(ExprToIntCast x) {
                return 1 + x.expression().accept(this);
            }

            @Override
            public Integer visit(UnaryExpression x) {
                return 1 + x.expression().accept(this);
            }

            @Override
            public Integer visit(UnaryIntExpression x) {
                return 1 + x.intExpr().accept(this);
            }

            @Override
            public Integer visit(MultiplicityFormula x) {
                return 1 + x.expression().accept(this);
            }

            @Override
            public Integer visit(BinaryExpression x) {
                return 1 + max(x.left().accept(this), x.right().accept(this));
            }

            @Override
            public Integer visit(ComparisonFormula x) {
                return 1 + max(x.left().accept(this), x.right().accept(this));
            }

            @Override
            public Integer visit(BinaryFormula x) {
                return 1 + max(x.left().accept(this), x.right().accept(this));
            }

            @Override
            public Integer visit(BinaryIntExpression x) {
                return 1 + max(x.left().accept(this), x.right().accept(this));
            }

            @Override
            public Integer visit(IntComparisonFormula x) {
                return 1 + max(x.left().accept(this), x.right().accept(this));
            }

            @Override
            public Integer visit(IfExpression x) {
                return 1 + max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
            }

            @Override
            public Integer visit(IfIntExpression x) {
                return 1 + max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
            }

            @Override
            public Integer visit(SumExpression x) {
                return 1 + max(x.decls().accept(this), x.intExpr().accept(this));
            }

            @Override
            public Integer visit(QuantifiedFormula x) {
                return 1 + max(x.decls().accept(this), x.formula().accept(this));
            }

            @Override
            public Integer visit(FixFormula x) {
                return 1 + max(x.condition().accept(this), x.formula().accept(this));
            }

            @Override
            public Integer visit(Comprehension x) {
                return 1 + max(x.decls().accept(this), x.formula().accept(this));
            }

            @Override
            public Integer visit(Decls x) {
                int max = 0, n = x.size();
                for (int i = 0; i < n; i++)
                    max = max(max, x.get(i).accept(this));
                return max;
            }

            @Override
            public Integer visit(ProjectExpression x) {
                int max = x.expression().accept(this);
                for (Iterator<IntExpression> t = x.columns(); t.hasNext();) {
                    max = max(max, t.next().accept(this));
                }
                return max;
            }

            @Override
            public Integer visit(RelationPredicate x) {
                if (x instanceof Function) {
                    Function f = ((Function) x);
                    return max(f.domain().accept(this), f.range().accept(this));
                }
                return 1;
            }

            @Override
            public Integer visit(NaryExpression x) {
                int max = 0;
                for (int m = 0, n = x.size(), i = 0; i < n; i++) {
                    m = x.child(i).accept(this);
                    if (i == 0 || max < m)
                        max = m;
                }
                return max + 1;
            }

            @Override
            public Integer visit(NaryIntExpression x) {
                int max = 0;
                for (int m = 0, n = x.size(), i = 0; i < n; i++) {
                    m = x.child(i).accept(this);
                    if (i == 0 || max < m)
                        max = m;
                }
                return max + 1;
            }

            @Override
            public Integer visit(NaryFormula x) {
                int max = 0;
                for (int m = 0, n = x.size(), i = 0; i < n; i++) {
                    m = x.child(i).accept(this);
                    if (i == 0 || max < m)
                        max = m;
                }
                return max + 1;
            }
        };
        Object ans = node.accept(vis);
        if (ans instanceof Integer)
            return ((Integer) ans).intValue();
        else
            return 0;
    }

    /**
     * Given a Kodkod formula node, return a Java program that (when compiled and
     * executed) would solve that formula.
     * <p>
     * Requirement: atoms must be String objects (since we cannot possibly output a
     * Java source code that can re-generate arbitrary Java objects).
     *
     * @param formula - the formula to convert
     * @param bitwidth - the integer bitwidth
     * @param atoms - an iterator over the set of all atoms
     * @param bounds - the Kodkod bounds object to use
     * @param atomMap - if nonnull, it is used to map the atom name before printing
     */
    public static String convert(Formula formula, int bitwidth, Iterable<String> atoms, Bounds bounds, Map<Object,String> atomMap) {
        StringWriter string = new StringWriter();
        PrintWriter file = new PrintWriter(string);
        new TranslateKodkodToJava(file, formula, bitwidth, atoms, bounds, atomMap);
        if (file.checkError()) {
            return ""; // shouldn't happen
        } else {
            return string.toString();
        }
    }

    /** The PrintWriter that is receiving the text. */
    private final PrintWriter                  file;

    /** This caches nodes that we have already generated. */
    private final IdentityHashMap<Node,String> map = new IdentityHashMap<Node,String>();

    /**
     * Given a node, return its name (if no name has been chosen, then make a new
     * name)
     */
    private String makename(Node obj) {
        if (map.containsKey(obj))
            return null;
        String name = "x" + (map.size());
        map.put(obj, name);
        return name;
    }

    /**
     * Given a node, call the visitor to dump its text out, then return its name.
     */
    private String make(Node x) {
        x.accept(this);
        return map.get(x);
    }

    /**
     * Constructor is private, so that the only way to access this class is via the
     * static convert() method.
     */
    private TranslateKodkodToJava(PrintWriter pw, Formula x, int bitwidth, Iterable<String> atoms, Bounds bounds, Map<Object,String> atomMap) {
        file = pw;
        file.printf("import java.util.Arrays;%n");
        file.printf("import java.util.List;%n");
        file.printf("import kodkod.ast.*;%n");
        file.printf("import kodkod.ast.operator.*;%n");
        file.printf("import kodkod.instance.*;%n");
        file.printf("import kodkod.engine.*;%n");
        file.printf("import kodkod.engine.satlab.SATFactory;%n");
        file.printf("import kodkod.engine.config.Options;%n%n");

        file.printf("/* %n");
        file.printf("  ==================================================%n");
        file.printf("    kodkod formula: %n");
        file.printf("  ==================================================%n");
        file.print(PrettyPrinter.print(x, 4) + "\n");
        file.printf("  ==================================================%n");
        file.printf("*/%n");
        file.printf("public final class Test {%n%n");
        file.printf("public static void main(String[] args) throws Exception {%n%n");
        ArrayList<String> atomlist = new ArrayList<String>();
        for (Object a : atoms) {
            String b = atomMap == null ? null : atomMap.get(a);
            atomlist.add(b == null ? a.toString() : b);
        }
        Collections.sort(atomlist);
        for (Relation r : bounds.relations()) {
            String name = makename(r);
            int a = r.arity();
            if (a == 1)
                file.printf("Relation %s = Relation.unary(\"%s\");%n", name, r.name());
            else
                file.printf("Relation %s = Relation.nary(\"%s\", %d);%n", name, r.name(), a);
        }
        file.printf("%nList<String> atomlist = Arrays.asList(%n");
        int j = (-1);
        for (String a : atomlist) {
            if (j != (-1))
                file.printf(",");
            else
                j = 0;
            if (j == 5) {
                file.printf("%n ");
                j = 0;
            } else {
                file.printf(" ");
                j++;
            }
            file.printf("\"%s\"", a);
        }
        file.printf("%n);%n%n");
        file.printf("Universe universe = new Universe(atomlist);%n");
        file.printf("TupleFactory factory = universe.factory();%n");
        file.printf("Bounds bounds = new Bounds(universe);%n%n");
        for (Relation r : bounds.relations()) {
            String n = map.get(r);
            TupleSet upper = bounds.upperBound(r);
            TupleSet lower = bounds.lowerBound(r);
            printTupleset(n + "_upper", upper, atomMap);
            if (upper.equals(lower)) {
                file.printf("bounds.boundExactly(%s, %s_upper);%n%n", n, n);
            } else if (lower.size() == 0) {
                file.printf("bounds.bound(%s, %s_upper);%n%n", n, n);
            } else {
                printTupleset(n + "_lower", lower, atomMap);
                file.printf("bounds.bound(%s, %s_lower, %s_upper);%n%n", n, n, n);
            }
        }
        for (IndexedEntry<TupleSet> i : bounds.intBounds()) {
            for (Tuple t : i.value()) {
                Object a = t.atom(0);
                String b = (atomMap != null ? atomMap.get(a) : null);
                String c = (b != null ? b : a.toString());
                file.printf("bounds.boundExactly(%d,factory.range(" + "factory.tuple(\"%s\"),factory.tuple(\"%s\")));%n", i.index(), c, c);
            }
        }
        file.printf("%n");
        String result = make(x);
        file.printf("%nSolver solver = new Solver();");
        file.printf("%nsolver.options().setSolver(SATFactory.DefaultSAT4J);");
        file.printf("%nsolver.options().setBitwidth(%d);", bitwidth != 0 ? bitwidth : 1);
        file.printf("%nsolver.options().setFlatten(false);");
        file.printf("%nsolver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);");
        file.printf("%nsolver.options().setSymmetryBreaking(20);");
        file.printf("%nsolver.options().setSkolemDepth(0);");
        file.printf("%nSystem.out.println(\"Solving...\");");
        file.printf("%nSystem.out.flush();");
        file.printf("%nSolution sol = solver.solve(%s,bounds);", result);
        file.printf("%nSystem.out.println(sol.toString());");
        file.printf("%n}}%n");
        file.close();
    }

    /** Print the tupleset using the name n. */
    private void printTupleset(String n, TupleSet ts, Map<Object,String> atomMap) {
        file.printf("TupleSet %s = factory.noneOf(%d);%n", n, ts.arity());
        for (Tuple t : ts) {
            file.printf("%s.add(", n);
            for (int i = 0; i < ts.arity(); i++) {
                if (i != 0)
                    file.printf(".product(");
                Object a = t.atom(i);
                String b = atomMap == null ? null : atomMap.get(a);
                file.printf("factory.tuple(\"%s\")", (b == null ? a.toString() : b));
                if (i != 0)
                    file.printf(")");
            }
            file.printf(");%n");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Relation x) {
        if (!map.containsKey(x))
            throw new RuntimeException("Unknown kodkod relation \"" + x.name() + "\" encountered");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(BinaryExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String left = make(x.left());
        String right = make(x.right());
        switch (x.op()) {
            case DIFFERENCE :
                file.printf("Expression %s=%s.difference(%s);%n", newname, left, right);
                break;
            case INTERSECTION :
                file.printf("Expression %s=%s.intersection(%s);%n", newname, left, right);
                break;
            case JOIN :
                file.printf("Expression %s=%s.join(%s);%n", newname, left, right);
                break;
            case OVERRIDE :
                file.printf("Expression %s=%s.override(%s);%n", newname, left, right);
                break;
            case PRODUCT :
                file.printf("Expression %s=%s.product(%s);%n", newname, left, right);
                break;
            case UNION :
                file.printf("Expression %s=%s.union(%s);%n", newname, left, right);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(ComparisonFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String left = make(x.left());
        String right = make(x.right());
        switch (x.op()) {
            case EQUALS :
                file.printf("Formula %s=%s.eq(%s);%n", newname, left, right);
                break;
            case SUBSET :
                file.printf("Formula %s=%s.in(%s);%n", newname, left, right);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(ProjectExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String expr = make(x.expression());
        List<String> names = new ArrayList<String>();
        for (Iterator<IntExpression> i = x.columns(); i.hasNext();) {
            names.add(make(i.next()));
        }
        for (int i = 0; i < names.size(); i++) {
            if (i == 0)
                file.printf("Expression %s=%s.project(", newname, expr);
            else
                file.printf(",");
            file.printf("%s", names.get(i));
        }
        file.printf(");%n");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(IntComparisonFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String left = make(x.left());
        String right = make(x.right());
        switch (x.op()) {
            case NEQ :
                file.printf("Formula %s=%s.neq(%s);%n", newname, left, right);
                break;
            case EQ :
                file.printf("Formula %s=%s.eq(%s);%n", newname, left, right);
                break;
            case GT :
                file.printf("Formula %s=%s.gt(%s);%n", newname, left, right);
                break;
            case GTE :
                file.printf("Formula %s=%s.gte(%s);%n", newname, left, right);
                break;
            case LT :
                file.printf("Formula %s=%s.lt(%s);%n", newname, left, right);
                break;
            case LTE :
                file.printf("Formula %s=%s.lte(%s);%n", newname, left, right);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(BinaryFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String left = make(x.left());
        String right = make(x.right());
        switch (x.op()) {
            case AND :
                file.printf("Formula %s=%s.and(%s);%n", newname, left, right);
                break;
            case OR :
                file.printf("Formula %s=%s.or(%s);%n", newname, left, right);
                break;
            case IMPLIES :
                file.printf("Formula %s=%s.implies(%s);%n", newname, left, right);
                break;
            case IFF :
                file.printf("Formula %s=%s.iff(%s);%n", newname, left, right);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(BinaryIntExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String left = make(x.left());
        String right = make(x.right());
        switch (x.op()) {
            case PLUS :
                file.printf("IntExpression %s=%s.plus(%s);%n", newname, left, right);
                break;
            case MINUS :
                file.printf("IntExpression %s=%s.minus(%s);%n", newname, left, right);
                break;
            case MULTIPLY :
                file.printf("IntExpression %s=%s.multiply(%s);%n", newname, left, right);
                break;
            case DIVIDE :
                file.printf("IntExpression %s=%s.divide(%s);%n", newname, left, right);
                break;
            case MODULO :
                file.printf("IntExpression %s=%s.modulo(%s);%n", newname, left, right);
                break;
            case AND :
                file.printf("IntExpression %s=%s.and(%s);%n", newname, left, right);
                break;
            case OR :
                file.printf("IntExpression %s=%s.or(%s);%n", newname, left, right);
                break;
            case XOR :
                file.printf("IntExpression %s=%s.xor(%s);%n", newname, left, right);
                break;
            case SHA :
                file.printf("IntExpression %s=%s.sha(%s);%n", newname, left, right);
                break;
            case SHL :
                file.printf("IntExpression %s=%s.shl(%s);%n", newname, left, right);
                break;
            case SHR :
                file.printf("IntExpression %s=%s.shr(%s);%n", newname, left, right);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(UnaryIntExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.intExpr());
        switch (x.op()) {
            case MINUS :
                file.printf("IntExpression %s=%s.negate();%n", newname, sub);
                break;
            case NOT :
                file.printf("IntExpression %s=%s.not();%n", newname, sub);
                break;
            case ABS :
                file.printf("IntExpression %s=%s.abs();%n", newname, sub);
                break;
            case SGN :
                file.printf("IntExpression %s=%s.signum();%n", newname, sub);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(UnaryExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.expression());
        switch (x.op()) {
            case CLOSURE :
                file.printf("Expression %s=%s.closure();%n", newname, sub);
                break;
            case REFLEXIVE_CLOSURE :
                file.printf("Expression %s=%s.reflexiveClosure();%n", newname, sub);
                break;
            case TRANSPOSE :
                file.printf("Expression %s=%s.transpose();%n", newname, sub);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(IfExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String a = make(x.condition());
        String b = make(x.thenExpr());
        String c = make(x.elseExpr());
        file.printf("Expression %s=%s.thenElse(%s,%s);%n", newname, a, b, c);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(IfIntExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String a = make(x.condition());
        String b = make(x.thenExpr());
        String c = make(x.elseExpr());
        file.printf("IntExpression %s=%s.thenElse(%s,%s);%n", newname, a, b, c);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(NotFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.formula());
        file.printf("Formula %s=%s.not();%n", newname, sub);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(IntToExprCast x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.intExpr());
        switch (x.op()) {
            case INTCAST :
                file.printf("Expression %s=%s.toExpression();%n", newname, sub);
                break;
            case BITSETCAST :
                file.printf("Expression %s=%s.toBitset();%n", newname, sub);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(ExprToIntCast x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.expression());
        switch (x.op()) {
            case CARDINALITY :
                file.printf("IntExpression %s=%s.count();%n", newname, sub);
                break;
            case SUM :
                file.printf("IntExpression %s=%s.sum();%n", newname, sub);
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(IntConstant x) {
        String newname = makename(x);
        if (newname == null)
            return;
        file.printf("IntExpression %s=IntConstant.constant(%d);%n", newname, x.value());
    }

    /** {@inheritDoc} */
    @Override
    public void visit(ConstantFormula x) {
        if (map.containsKey(x))
            return;
        String newname = (x.booleanValue() ? "Formula.TRUE" : "Formula.FALSE");
        map.put(x, newname);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(ConstantExpression x) {
        if (map.containsKey(x))
            return;
        String newname = null;
        if (x == Expression.NONE)
            newname = "Expression.NONE";
        else if (x == Expression.UNIV)
            newname = "Expression.UNIV";
        else if (x == Expression.IDEN)
            newname = "Expression.IDEN";
        else if (x == Expression.INTS)
            newname = "Expression.INTS";
        else
            throw new RuntimeException("Unknown kodkod ConstantExpression \"" + x + "\" encountered");
        map.put(x, newname);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Variable x) {
        String newname = makename(x);
        if (newname == null)
            return;
        int a = x.arity();
        if (a == 1)
            file.printf("Variable %s=Variable.unary(\"%s\");%n", newname, x.name());
        else
            file.printf("Variable %s=Variable.nary(\"%s\",%d);%n", newname, x.name(), a);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Comprehension x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String d = make(x.decls());
        String f = make(x.formula());
        file.printf("Expression %s=%s.comprehension(%s);%n", newname, f, d);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(QuantifiedFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String d = make(x.decls());
        String f = make(x.formula());
        switch (x.quantifier()) {
            case ALL :
                file.printf("Formula %s=%s.forAll(%s);%n", newname, f, d);
                break;
            case SOME :
                file.printf("Formula %s=%s.forSome(%s);%n", newname, f, d);
                break;
            default :
                throw new RuntimeException("Unknown kodkod quantifier \"" + x.quantifier() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(FixFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String f = make(x.formula());
        String c = make(x.condition());
        file.printf("Formula %s=%s.fix(%s);%n", newname, f, c);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(SumExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String d = make(x.decls());
        String f = make(x.intExpr());
        file.printf("IntExpression %s=%s.sum(%s);%n", newname, f, d);
    }

    /** {@inheritDoc} */
    @Override
    public void visit(MultiplicityFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String sub = make(x.expression());
        switch (x.multiplicity()) {
            case LONE :
                file.printf("Formula %s=%s.lone();%n", newname, sub);
                break;
            case ONE :
                file.printf("Formula %s=%s.one();%n", newname, sub);
                break;
            case SOME :
                file.printf("Formula %s=%s.some();%n", newname, sub);
                break;
            case NO :
                file.printf("Formula %s=%s.no();%n", newname, sub);
                break;
            default :
                throw new RuntimeException("Unknown kodkod multiplicity \"" + x.multiplicity() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Decl x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String v = make(x.variable());
        String e = make(x.expression());
        switch (x.multiplicity()) {
            case LONE :
                file.printf("Decls %s=%s.loneOf(%s);%n", newname, v, e);
                break;
            case ONE :
                file.printf("Decls %s=%s.oneOf(%s);%n", newname, v, e);
                break;
            case SOME :
                file.printf("Decls %s=%s.someOf(%s);%n", newname, v, e);
                break;
            case SET :
                file.printf("Decls %s=%s.setOf(%s);%n", newname, v, e);
                break;
            default :
                throw new RuntimeException("Unknown kodkod multiplicity \"" + x.multiplicity() + "\" encountered");
        }
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Decls x) {
        String newname = makename(x);
        if (newname == null)
            return;
        for (Decl y : x) {
            y.accept(this);
        }
        boolean first = true;
        file.printf("Decls %s=", newname);
        for (Decl y : x) {
            String z = map.get(y);
            if (first) {
                file.printf("%s", z);
                first = false;
            } else
                file.printf(".and(%s)", z);
        }
        file.printf(";%n");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(RelationPredicate x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String rel = make(x.relation());
        switch (x.name()) {
            case TOTAL_ORDERING : {
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) x;
                String o = make(tp.ordered());
                String f = make(tp.first());
                String l = make(tp.last());
                file.printf("Formula %s=%s.totalOrder(%s,%s,%s);%n", newname, rel, o, f, l);
                return;
            }
            case FUNCTION : {
                final RelationPredicate.Function tp = (RelationPredicate.Function) x;
                String domain = make(tp.domain());
                String range = make(tp.range());
                switch (((RelationPredicate.Function) x).targetMult()) {
                    case ONE :
                        file.printf("Formula %s=%s.function(%s,%s);%n", newname, rel, domain, range);
                        return;
                    case LONE :
                        file.printf("Formula %s=%s.partialFunction(%s,%s);%n", newname, rel, domain, range);
                        return;
                    default :
                        throw new RuntimeException("Illegal multiplicity encountered in RelationPredicate.Function");
                }
            }
            case ACYCLIC : {
                file.printf("Formula %s=%s.acyclic();%n", newname, rel);
                return;
            }
        }
        throw new RuntimeException("Unknown RelationPredicate \"" + x + "\" encountered");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(NaryExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String[] list = new String[x.size()];
        for (int i = 0; i < list.length; i++)
            list[i] = make(x.child(i));
        file.printf("Expression %s=Expression.compose(ExprOperator.", newname);
        switch (x.op()) {
            case INTERSECTION :
                file.print("INTERSECTION");
                break;
            case OVERRIDE :
                file.print("OVERRIDE");
                break;
            case PRODUCT :
                file.print("PRODUCT");
                break;
            case UNION :
                file.print("UNION");
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
        for (int i = 0; i < list.length; i++)
            file.printf(", %s", list[i]);
        file.printf(");%n");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(NaryIntExpression x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String[] list = new String[x.size()];
        for (int i = 0; i < list.length; i++)
            list[i] = make(x.child(i));
        file.printf("IntExpression %s=IntExpression.compose(IntOperator.", newname);
        switch (x.op()) {
            case PLUS :
                file.print("PLUS");
                break;
            case MULTIPLY :
                file.print("MULTIPLY");
                break;
            case AND :
                file.print("AND");
                break;
            case OR :
                file.print("OR");
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
        for (int i = 0; i < list.length; i++)
            file.printf(", %s", list[i]);
        file.printf(");%n");
    }

    /** {@inheritDoc} */
    @Override
    public void visit(NaryFormula x) {
        String newname = makename(x);
        if (newname == null)
            return;
        String[] list = new String[x.size()];
        for (int i = 0; i < list.length; i++)
            list[i] = make(x.child(i));
        file.printf("Formula %s=Formula.compose(FormulaOperator.", newname);
        switch (x.op()) {
            case AND :
                file.print("AND");
                break;
            case OR :
                file.print("OR");
                break;
            default :
                throw new RuntimeException("Unknown kodkod operator \"" + x.op() + "\" encountered");
        }
        for (int i = 0; i < list.length; i++)
            file.printf(", %s", list[i]);
        file.printf(");%n");
    }
}
