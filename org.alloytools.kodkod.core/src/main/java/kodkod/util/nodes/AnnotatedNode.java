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

import static kodkod.ast.RelationPredicate.Name.ACYCLIC;
import static kodkod.ast.RelationPredicate.Name.FUNCTION;
import static kodkod.ast.RelationPredicate.Name.TOTAL_ORDERING;
import static kodkod.ast.operator.FormulaOperator.AND;
import static kodkod.ast.operator.FormulaOperator.IMPLIES;
import static kodkod.ast.operator.FormulaOperator.OR;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.List;
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
import kodkod.ast.operator.ExprCastOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.util.collections.ArrayStack;
import kodkod.util.collections.IdentityHashSet;
import kodkod.util.collections.Stack;

/**
 * A node annotated with information about structural sharing in its ast/dag.
 * The class also provides utility methods for collecting various information
 * about annotated nodes.
 *
 * @specfield node: N // annotated node
 * @specfield source: node.*components ->one Node // maps the subnodes of
 *            this.node to nodes from // which they were derived by some
 *            transformation process // (e.g. skolemization, predicate inlining)
 * @author Emina Torlak
 */
public final class AnnotatedNode<N extends Node> {

    private final N                                    node;
    private final Set<Node>                            sharedNodes;
    private final Map< ? extends Node, ? extends Node> source;
    private Map< ? extends Node,Boolean>               holAnnotations;

    /**
     * Constructs a new annotator for the given node.
     *
     * @ensures this.node' = node && this.source' = node.*components<:iden
     */
    private AnnotatedNode(N node) {
        this.node = node;
        final SharingDetector detector = new SharingDetector();
        node.accept(detector);
        this.sharedNodes = Collections.unmodifiableSet(detector.sharedNodes());
        this.source = Collections.emptyMap();
    }

    /**
     * Constructs a new annotator for the given node and source map.
     *
     * @ensures this.node' = node && this.source' = node.*components<:iden ++ source
     */
    private AnnotatedNode(N node, Map< ? extends Node, ? extends Node> source) {
        this.node = node;
        final SharingDetector detector = new SharingDetector();
        node.accept(detector);
        this.sharedNodes = Collections.unmodifiableSet(detector.sharedNodes());
        this.source = source;
    }

    public boolean hasHOLannotations() {
        return holAnnotations != null;
    }

    public void annotateHOL() {
        HOLAnnotator a = new HOLAnnotator();
        this.node.accept(a);
        holAnnotations = a.holAnnotations;
    }

    public boolean isHOLNode(Node n) {
        assert holAnnotations != null : "not annotated for HOL";
        Boolean ans = holAnnotations != null ? holAnnotations.get(n) : null;
        // assert ans != null : "node " + n + " not found in holAnnotations";
        return !Boolean.FALSE.equals(ans);
    }

    public boolean isFOLNode(Node n) {
        return !isHOLNode(n);
    }

    /**
     * Returns an annotation for the given node. The source map of the returned
     * annotation object maps each descendant of the node to itself.
     *
     * @return { a: AnnotatedNode<N> | a.node = node && a.source =
     *         node.*components<:iden }
     */
    public static <N extends Node> AnnotatedNode<N> annotate(N node) {
        return new AnnotatedNode<N>(node);
    }

    /**
     * Returns an annotation for the given node. The source map of the returned
     * annotation object maps each descendant of the node to its value in the given
     * source map, or to itself if the given source map has no value for that
     * descendant.
     *
     * @return { a: AnnotatedNode<N> | a.node = node && a.source =
     *         (node.*components<:iden) ++ source }
     */
    public static <N extends Node> AnnotatedNode<N> annotate(N node, Map< ? extends Node, ? extends Node> source) {
        return new AnnotatedNode<N>(node, source);
    }

    /**
     * Returns an annotation for an n-ary conjunctions of
     * {@linkplain Nodes#roots(Formula) roots} of the given formula. The source map
     * of the returned annotation object maps each descendant of the node to itself.
     * The root conjunction itself is mapped to the input formula.
     *
     * @return { a: AnnotatedNode<Formula> | a.node =
     *         Formula.and(Nodes.roots(formula)) && a.source =
     *         (node.^components<:iden) + a.node->formula }
     */
    public static AnnotatedNode<Formula> annotateRoots(Formula formula) {
        final Formula flat = Formula.and(Nodes.roots(formula));
        return new AnnotatedNode<Formula>(flat, Collections.singletonMap(flat, formula));
    }

    /**
     * Returns this.node.
     *
     * @return this.node
     */
    public final N node() {
        return node;
    }

    /**
     * Returns the source of the the given descendant of this.node.
     *
     * @requires n in this.node.*components
     * @return this.source[n]
     */
    public final Node sourceOf(Node n) {
        final Node d = source.get(n);
        return d == null ? n : d;
    }

    /**
     * Returns the set of all non-leaf descendants of this.node that have more than
     * one parent.
     *
     * @return {n: Node | some n.children && #(n.~components &
     *         this.node.*components) > 1 }
     */
    public final Set<Node> sharedNodes() {
        return sharedNodes;
    }

    /**
     * Returns the set of all relations at the leaves of this annotated node.
     *
     * @return Relation & this.node.*components
     */
    public final Set<Relation> relations() {
        final Set<Relation> relations = new IdentityHashSet<Relation>();
        final AbstractVoidVisitor visitor = new AbstractVoidVisitor() {

            private final Set<Node> visited = new IdentityHashSet<Node>(sharedNodes.size());

            @Override
            protected boolean visited(Node n) {
                return sharedNodes.contains(n) && !visited.add(n);
            }

            @Override
            public void visit(Relation relation) {
                relations.add(relation);
            }
        };
        node.accept(visitor);
        return relations;
    }

    public final Set<Relation> atomRelations() {
        final Set<Relation> ans = new IdentityHashSet<Relation>();
        for (Relation r : relations())
            if (r.isAtom())
                ans.add(r);
        return ans;
    }

    public final Set<Relation> skolemRelations() {
        final Set<Relation> ans = new IdentityHashSet<Relation>();
        for (Relation r : relations())
            if (r.isSkolem())
                ans.add(r);
        return ans;
    }

    /**
     * Returns true if this.node contains a child whose meaning depends on integer
     * bounds (i.e. an ExprToIntCast node with SUM operator or an IntToExprCast node
     * or Expression.INTS constant).
     *
     * @return true if this.node contains a child whose meaning depends on integer
     *         bounds (i.e. an ExprToIntCast node with SUM operator or an
     *         IntToExprCast node or Expression.INTS constant).
     */
    public final boolean usesInts() {
        final AbstractDetector detector = new AbstractDetector(sharedNodes) {

            @Override
            public Boolean visit(IntToExprCast expr) {
                return cache(expr, Boolean.TRUE);
            }

            @Override
            public Boolean visit(ExprToIntCast intExpr) {
                if (intExpr.op() == ExprCastOperator.CARDINALITY)
                    super.visit(intExpr);
                return cache(intExpr, Boolean.TRUE);
            }

            @Override
            public Boolean visit(ConstantExpression expr) {
                return expr == Expression.INTS ? Boolean.TRUE : Boolean.FALSE;
            }
        };
        return (Boolean) node.accept(detector);
    }

    /**
     * Returns a map of RelationPredicate names to sets of top-level relation
     * predicates with the corresponding names in this.node.
     *
     * @return a map of RelationPredicate names to sets of top-level relation
     *         predicates with the corresponding names in this.node. A predicate is
     *         considered 'top-level' if it is a component of the top-level
     *         conjunction, if any, of this.node.
     */
    public final Map<RelationPredicate.Name,Set<RelationPredicate>> predicates() {
        final PredicateCollector collector = new PredicateCollector(sharedNodes);
        node.accept(collector);
        return collector.preds;
    }

    /**
     * Returns a Detector that will return TRUE when applied to a descendent of
     * this.node iff the descendent contains a quantified formula.
     *
     * @return a Detector that will return TRUE when applied to a descendent of
     *         this.node iff the descendent contains a quantified formula.
     */
    public final AbstractDetector quantifiedFormulaDetector() {
        return new AbstractDetector(sharedNodes) {

            @Override
            public Boolean visit(QuantifiedFormula quantFormula) {
                return cache(quantFormula, true);
            }
        };
    }

    /**
     * Returns a Detector that will return TRUE when applied to a descendent of
     * this.node iff the descendent contains a free variable.
     *
     * @return a Detector that will return TRUE when applied to a descendent of
     *         this.node iff the descendent contains a free variable.
     */
    public final AbstractDetector freeVariableDetector() {
        return new FreeVariableDetector(sharedNodes);
    }

    /**
     * Returns a string representation of this annotated node.
     *
     * @return string representation of this annotated node.
     */
    @Override
    public String toString() {
        final StringBuilder ret = new StringBuilder();
        ret.append("node: ");
        ret.append(node);
        ret.append("\nshared nodes: ");
        ret.append(sharedNodes);
        ret.append("\nsources: ");
        ret.append(source);
        return ret.toString();
    }

    /**
     * Detects shared non-leaf descendents of a given node.
     *
     * @specfield node: Node // node to which the analyzer is applied
     */
    private static final class SharingDetector extends AbstractVoidVisitor {

        /*
         * maps each internal node with more than one parent to TRUE and all other
         * internal nodes to FALSE
         */
        final IdentityHashMap<Node,Boolean> sharingStatus;
        /* @invariant numShareNodes = #sharingStatus.TRUE */
        int                                 numSharedNodes;

        SharingDetector() {
            sharingStatus = new IdentityHashMap<Node,Boolean>();
        }

        /**
         * Returns the shared internal nodes of this.node. This method should be called
         * only after this visitor has been applied to this.node.
         *
         * @return {n: Node | #(n.~children & node.*children) > 1 }
         */
        IdentityHashSet<Node> sharedNodes() {
            final IdentityHashSet<Node> shared = new IdentityHashSet<Node>(numSharedNodes);
            for (Map.Entry<Node,Boolean> entry : sharingStatus.entrySet()) {
                if (entry.getValue() == Boolean.TRUE)
                    shared.add(entry.getKey());
            }
            return shared;
        }

        /**
         * Records the visit to the given node in the status map. If the node has not
         * been visited before, it is mapped to Boolean.FALSE and false is returned.
         * Otherwise, it is mapped to Boolean.TRUE and true is returned. The first time
         * a Node is mapped to true, numSharedNodes is incremented by one.
         *
         * @ensures no this.shared[node] => this.shared' = this.shared + node->FALSE,
         *          this.shared[node] = FALSE => this.shared' = this.shared +
         *          node->TRUE, this.shared' = this.shared
         * @return this.shared'[node]
         */
        @Override
        protected final boolean visited(Node node) {
            Boolean status = sharingStatus.get(node);
            if (!Boolean.TRUE.equals(status)) {
                if (status == null) {
                    status = Boolean.FALSE;
                } else { // status == Boolean.FALSE
                    status = Boolean.TRUE;
                    numSharedNodes++;
                }
                sharingStatus.put(node, status);
            }
            return status;
        }
    }

    /**
     * A visitor that detects free variables of a node.
     *
     * @author Emina Torlak
     */
    private static final class FreeVariableDetector extends AbstractDetector {
        /*
         * Holds the variables that are currently in scope, with the variable at the top
         * of the stack being the last declared variable.
         */

        private final Stack<Variable> varsInScope = new ArrayStack<Variable>();

        /**
         * Constructs a new free variable detector.
         */
        FreeVariableDetector(Set<Node> sharedNodes) {
            super(sharedNodes);
        }

        /**
         * Visits the given comprehension, quantified formula, or sum expression. The
         * method returns TRUE if the creator body contains any variable not bound by
         * the decls; otherwise returns FALSE.
         */
        private Boolean visit(Node creator, Decls decls, Node body) {
            Boolean ret = lookup(creator);
            if (ret != null)
                return ret;
            boolean retVal = false;
            for (Decl decl : decls) {
                retVal = decl.expression().accept(this) || retVal;
                varsInScope.push(decl.variable());
            }
            retVal = ((Boolean) body.accept(this)) || retVal;
            for (int i = decls.size(); i > 0; i--) {
                varsInScope.pop();
            }
            return cache(creator, retVal);
        }

        /**
         * Returns TRUE if the given variable is free in its parent, otherwise returns
         * FALSE.
         *
         * @return TRUE if the given variable is free in its parent, otherwise returns
         *         FALSE.
         */
        @Override
        public Boolean visit(Variable variable) {
            return Boolean.valueOf(varsInScope.search(variable) < 0);
        }

        @Override
        public Boolean visit(Decl decl) {
            Boolean ret = lookup(decl);
            if (ret != null)
                return ret;
            return cache(decl, decl.expression().accept(this));
        }

        @Override
        public Boolean visit(Comprehension comprehension) {
            return visit(comprehension, comprehension.decls(), comprehension.formula());
        }

        @Override
        public Boolean visit(SumExpression intExpr) {
            return visit(intExpr, intExpr.decls(), intExpr.intExpr());
        }

        @Override
        public Boolean visit(QuantifiedFormula qformula) {
            return visit(qformula, qformula.decls(), qformula.formula());
        }
    }

    /**
     * A visitor that detects and collects top-level relation predicates; i.e.
     * predicates that are components in the top-level conjunction, if any, on ANY
     * path starting at the root.
     */
    private static final class PredicateCollector extends AbstractVoidVisitor {

        protected boolean                                            negated;
        private final Set<Node>                                      sharedNodes;
        /*
         * if a given node is not mapped at all, it means that it has not been visited;
         * if it is mapped to FALSE, it has been visited with negated=FALSE, if it is
         * mapped to TRUE, it has been visited with negated=TRUE, if it is mapped to
         * null, it has been visited with both values of negated.
         */
        private final Map<Node,Boolean>                              visited;
        /*
         * holds the top level predicates at the the end of the visit
         */
        final EnumMap<RelationPredicate.Name,Set<RelationPredicate>> preds;

        /**
         * Constructs a new collector.
         *
         * @ensures this.negated' = false
         */
        PredicateCollector(Set<Node> sharedNodes) {
            this.sharedNodes = sharedNodes;
            this.visited = new IdentityHashMap<Node,Boolean>();
            this.negated = false;
            preds = new EnumMap<RelationPredicate.Name,Set<RelationPredicate>>(RelationPredicate.Name.class);
            preds.put(ACYCLIC, new IdentityHashSet<RelationPredicate>(4));
            preds.put(TOTAL_ORDERING, new IdentityHashSet<RelationPredicate>(4));
            preds.put(FUNCTION, new IdentityHashSet<RelationPredicate>(8));
        }

        /**
         * Returns true if n has already been visited with the current value of the
         * negated flag; otherwise returns false.
         *
         * @ensures records that n is being visited with the current value of the
         *          negated flag
         * @return true if n has already been visited with the current value of the
         *         negated flag; otherwise returns false.
         */
        @Override
        protected final boolean visited(Node n) {
            if (sharedNodes.contains(n)) {
                if (!visited.containsKey(n)) { // first visit
                    visited.put(n, Boolean.valueOf(negated));
                    return false;
                } else {
                    final Boolean visit = visited.get(n);
                    if (visit == null || visit == negated) { // already visited
                                                            // with same
                                                            // negated value
                        return true;
                    } else { // already visited with different negated value
                        visited.put(n, null);
                        return false;
                    }
                }
            }
            return false;
        }

        /**
         * Calls visited(comp); comp's children are not top-level formulas so they are
         * not visited.
         */
        @Override
        public void visit(Comprehension comp) {
            visited(comp);
        }

        /**
         * Calls visited(ifexpr); ifexpr's children are not top-level formulas so they
         * are not visited.
         */
        @Override
        public void visit(IfExpression ifexpr) {
            visited(ifexpr);
        }

        /**
         * Calls visited(ifexpr); ifexpr's children are not top-level formulas so they
         * are not visited.
         */
        @Override
        public void visit(IfIntExpression ifexpr) {
            visited(ifexpr);
        }

        /**
         * Calls visited(intComp); intComp's children are not top-level formulas so they
         * are not visited.
         */
        @Override
        public void visit(IntComparisonFormula intComp) {
            visited(intComp);
        }

        /**
         * Calls visited(quantFormula); quantFormula's children are not top-level
         * formulas so they are not visited.
         */
        @Override
        public void visit(QuantifiedFormula quantFormula) {
            visited(quantFormula);
        }

        /**
         * Visits the children of the given formula if it has not been visited already
         * with the given value of the negated flag and if binFormula.op==IMPLIES &&
         * negated or binFormula.op==AND && !negated or binFormula.op==OR && negated.
         * Otherwise does nothing.
         *
         * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.BinaryFormula)
         */
        @Override
        public void visit(BinaryFormula binFormula) {
            if (visited(binFormula))
                return;
            final FormulaOperator op = binFormula.op();

            if ((!negated && op == AND) || (negated && op == OR)) { // op==AND
                                                                   // || op==OR
                binFormula.left().accept(this);
                binFormula.right().accept(this);
            } else if (negated && op == IMPLIES) { // !(a => b) = !(!a || b) = a
                                                  // && !b
                negated = !negated;
                binFormula.left().accept(this);
                negated = !negated;
                binFormula.right().accept(this);
            }
        }

        /**
         * Visits the children of the given formula if it has not been visited already
         * with the given value of the negated flag and if formula.op==OR && negated or
         * formula.op==AND && !negated. Otherwise does nothing.
         *
         * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.NaryFormula)
         */
        @Override
        public void visit(NaryFormula formula) {
            if (visited(formula))
                return;
            final FormulaOperator op = formula.op();
            if ((!negated && op == AND) || (negated && op == OR)) { // op==AND
                                                                   // || op==OR
                for (Formula child : formula) {
                    child.accept(this);
                }
            }
        }

        /**
         * Visits the children of the child of the child formula, with the negation of
         * the current value of the negated flag, if it has not already been visited
         * with the current value of this.negated; otherwise does nothing.
         */
        @Override
        public void visit(NotFormula not) {
            if (visited(not))
                return;
            negated = !negated;
            not.formula().accept(this);
            negated = !negated;
        }

        /**
         * Calls visited(compFormula); compFormula's children are not top-level formulas
         * so they are not visited.
         */
        @Override
        public void visit(ComparisonFormula compFormula) {
            visited(compFormula);
        }

        /**
         * Calls visited(multFormula); multFormula's child is not top-level formulas so
         * it is not visited.
         */
        @Override
        public void visit(MultiplicityFormula multFormula) {
            visited(multFormula);
        }

        /**
         * Records the visit to this predicate if it is not negated.
         */
        @Override
        public void visit(RelationPredicate pred) {
            if (visited(pred))
                return;
            if (!negated) {
                preds.get(pred.name()).add(pred);
            }
        }
    }

    static class HOLAnnotator implements ReturnVisitor<Boolean,Boolean,Boolean,Boolean> {

        private Map<Node,Boolean> holAnnotations = new IdentityHashMap<Node,Boolean>();

        private Boolean get(Node n) {
            return holAnnotations.get(n);
        }

        private Boolean place(Node n, Boolean b) {
            holAnnotations.put(n, b);
            return b;
        }

        private Boolean noHOL(Node n) {
            return place(n, Boolean.FALSE);
        }

        private <E extends Node> Boolean checkVisitedThenAccumA(Node n, Boolean acc, E... subs) {
            return checkVisitedThenAccum(n, acc, Arrays.asList(subs));
        }

        private <E extends Node> Boolean checkVisitedThenAccum(Node n, Boolean acc, Iterable<E> subs) {
            Boolean ans = get(n);
            if (ans != null)
                return ans;
            return accum(n, acc, subs);
        }

        private <E extends Node> Boolean accum(Node n, Boolean acc, Iterable<E> subs) {
            for (Node child : subs) {
                Boolean res = (Boolean) child.accept(this);
                acc = acc || res;
            }
            return place(n, acc);
        }

        @Override
        public Boolean visit(Decls decls) {
            return checkVisitedThenAccum(decls, Boolean.FALSE, decls);
        }

        @Override
        public Boolean visit(Decl decl) {
            return checkVisitedThenAccumA(decl, decl.multiplicity() != Multiplicity.ONE, decl.variable(), decl.expression());
        }

        @Override
        public Boolean visit(Relation relation) {
            return noHOL(relation);
        }

        @Override
        public Boolean visit(Variable variable) {
            return noHOL(variable);
        }

        @Override
        public Boolean visit(ConstantExpression constExpr) {
            return noHOL(constExpr);
        }

        @Override
        public Boolean visit(NaryExpression expr) {
            return checkVisitedThenAccum(expr, Boolean.FALSE, expr);
        }

        @Override
        public Boolean visit(BinaryExpression expr) {
            return checkVisitedThenAccumA(expr, Boolean.FALSE, expr.left(), expr.right());
        }

        @Override
        public Boolean visit(UnaryExpression expr) {
            return checkVisitedThenAccumA(expr, Boolean.FALSE, expr.expression());
        }

        @Override
        public Boolean visit(Comprehension cph) {
            return checkVisitedThenAccumA(cph, Boolean.FALSE, cph.decls(), cph.formula());
        }

        @Override
        public Boolean visit(IfExpression ife) {
            return checkVisitedThenAccumA(ife, Boolean.FALSE, ife.condition(), ife.thenExpr(), ife.elseExpr());
        }

        @Override
        public Boolean visit(ProjectExpression project) {
            Boolean ans = get(project);
            if (ans != null)
                return ans;
            List<IntExpression> cols = new ArrayList<IntExpression>(project.arity());
            for (int i = 0, arity = project.arity(); i < arity; i++) {
                cols.add(project.column(i));
            }
            return accum(project, project.expression().accept(this), cols);
        }

        @Override
        public Boolean visit(IntToExprCast castExpr) {
            return checkVisitedThenAccumA(castExpr, Boolean.FALSE, castExpr.intExpr());
        }

        @Override
        public Boolean visit(IntConstant intConst) {
            return noHOL(intConst);
        }

        @Override
        public Boolean visit(IfIntExpression e) {
            return checkVisitedThenAccumA(e, Boolean.FALSE, e.condition(), e.thenExpr(), e.elseExpr());
        }

        @Override
        public Boolean visit(ExprToIntCast e) {
            return checkVisitedThenAccumA(e, Boolean.FALSE, e.expression());
        }

        @Override
        public Boolean visit(NaryIntExpression e) {
            return checkVisitedThenAccum(e, Boolean.FALSE, e);
        }

        @Override
        public Boolean visit(BinaryIntExpression e) {
            return checkVisitedThenAccumA(e, Boolean.FALSE, e.left(), e.right());
        }

        @Override
        public Boolean visit(UnaryIntExpression e) {
            return checkVisitedThenAccumA(e, Boolean.FALSE, e.intExpr());
        }

        @Override
        public Boolean visit(SumExpression e) {
            return checkVisitedThenAccumA(e, Boolean.FALSE, e.decls(), e.intExpr());
        }

        @Override
        public Boolean visit(IntComparisonFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.left(), f.right());
        }

        @Override
        public Boolean visit(QuantifiedFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.decls(), f.formula());
        }

        @Override
        public Boolean visit(NaryFormula f) {
            return checkVisitedThenAccum(f, Boolean.FALSE, f);
        }

        @Override
        public Boolean visit(BinaryFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.left(), f.right());
        }

        @Override
        public Boolean visit(NotFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.formula());
        }

        @Override
        public Boolean visit(ConstantFormula cnst) {
            return noHOL(cnst);
        }

        @Override
        public Boolean visit(ComparisonFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.left(), f.right());
        }

        @Override
        public Boolean visit(MultiplicityFormula f) {
            return checkVisitedThenAccumA(f, Boolean.FALSE, f.expression());
        }

        @Override
        public Boolean visit(RelationPredicate pred) {
            Boolean ans = get(pred);
            if (ans != null)
                return ans;
            pred.relation().accept(this);
            if (pred.name() == RelationPredicate.Name.FUNCTION) {
                final RelationPredicate.Function fp = (RelationPredicate.Function) pred;
                fp.domain().accept(this);
                fp.range().accept(this);
            } else if (pred.name() == RelationPredicate.Name.TOTAL_ORDERING) {
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) pred;
                tp.ordered().accept(this);
                tp.first().accept(this);
                tp.last().accept(this);
            }
            return noHOL(pred);
        }

        @Override
        public Boolean visit(FixFormula f) {
            return checkVisitedThenAccumA(f, Boolean.TRUE, f.formula(), f.condition());
        }

    }

    public Map< ? extends Node, ? extends Node> sources() {
        return Collections.unmodifiableMap(this.source);
    }
}
