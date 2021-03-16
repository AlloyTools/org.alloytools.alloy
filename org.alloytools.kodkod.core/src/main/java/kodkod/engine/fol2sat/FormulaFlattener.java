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
package kodkod.engine.fol2sat;

import static kodkod.ast.operator.FormulaOperator.AND;
import static kodkod.ast.operator.FormulaOperator.IFF;
import static kodkod.ast.operator.FormulaOperator.IMPLIES;
import static kodkod.ast.operator.FormulaOperator.OR;
import static kodkod.ast.operator.Quantifier.ALL;
import static kodkod.ast.operator.Quantifier.SOME;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decls;
import kodkod.ast.Formula;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.RelationPredicate;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Flattens a given formula by putting into negation normal form and,
 * optionally, by breaking up universally quantifier formulas whenever possible.
 *
 * @author Emina Torlak
 */
public final class FormulaFlattener extends AbstractVoidVisitor {

    /**
     * Flattens the given formula into a set of conjuncts by pushing negations
     * through quantifier-free formulas, if breakupQuantifiers is false. Otherwise,
     * pushes the negations through all formulas, breaking up universal quantifiers
     * whenever possible. The source map of the returned annotated node reflects the
     * source relationships from the descendants of the returned formula to the
     * sources of the corresponding descendants of annotated.node.
     *
     * @return a map that binds each flattened conjuncts to the corresponding
     *         subformula of annotated.node
     */
    public static AnnotatedNode<Formula> flatten(AnnotatedNode<Formula> annotated, boolean breakupQuantifiers) {
        final FormulaFlattener flat = new FormulaFlattener(annotated.sharedNodes(), breakupQuantifiers);
        annotated.node().accept(flat);
        final List<Formula> roots = new ArrayList<Formula>(flat.conjuncts.size());
        roots.addAll(flat.conjuncts.keySet());
        for (Iterator<Map.Entry<Formula,Node>> itr = flat.conjuncts.entrySet().iterator(); itr.hasNext();) {
            final Map.Entry<Formula,Node> entry = itr.next();
            final Node source = annotated.sourceOf(entry.getValue());
            if (entry.getKey() == source) {
                itr.remove();
            } else {
                entry.setValue(source);
            }
        }
        return AnnotatedNode.annotate(Formula.and(roots), flat.conjuncts);
    }

    private Map<Formula,Node>       conjuncts;
    private final Map<Node,Boolean> visited;
    private final Set<Node>         shared;
    private boolean                 negated;
    private final boolean           breakupQuantifiers;

    /**
     * Constructs a flattener for a formula in which the given nodes are shared.
     */
    private FormulaFlattener(Set<Node> shared, boolean breakupQuantifiers) {
        this.conjuncts = new LinkedHashMap<Formula,Node>();
        this.shared = shared;
        this.visited = new IdentityHashMap<Node,Boolean>();
        this.negated = false;
        this.breakupQuantifiers = breakupQuantifiers;
    }

    /**
     * Returns the result of applying this visitor to the given annotated formula.
     *
     * @return the result of applying this visitor to the given annotated formula.
     */
    final AnnotatedNode<Formula> apply(AnnotatedNode<Formula> annotated) {
        annotated.node().accept(this);
        final List<Formula> roots = new ArrayList<Formula>(conjuncts.size());
        roots.addAll(conjuncts.keySet());
        for (Iterator<Map.Entry<Formula,Node>> itr = conjuncts.entrySet().iterator(); itr.hasNext();) {
            final Map.Entry<Formula,Node> entry = itr.next();
            final Node source = annotated.sourceOf(entry.getValue());
            if (entry.getKey() == source) {
                itr.remove();
            } else {
                entry.setValue(source);
            }
        }
        return AnnotatedNode.annotate(Formula.and(roots), conjuncts);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visited(kodkod.ast.Node)
     */
    @Override
    protected boolean visited(Node n) {
        if (shared.contains(n)) {
            if (visited.containsKey(n)) {
                final Boolean val = visited.get(n);
                if (val == null || val.booleanValue() == negated) {
                    return true;
                } else {
                    visited.put(n, null);
                    return false;
                }
            } else {
                visited.put(n, Boolean.valueOf(negated));
                return false;
            }
        }
        return false;
    }

    /**
     * Calls nf.formula.accept(this) after flipping the negation flag.
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.NotFormula)
     */
    @Override
    public final void visit(NotFormula nf) {
        if (visited(nf))
            return;

        final Map<Formula,Node> oldConjuncts = conjuncts;
        conjuncts = new LinkedHashMap<Formula,Node>();
        negated = !negated;
        nf.formula().accept(this);
        negated = !negated;
        if (conjuncts.size() > 1) { // was broken down further
            oldConjuncts.putAll(conjuncts);
            conjuncts = oldConjuncts;
        } else { // wasn't broken down further
            conjuncts = oldConjuncts;
            conjuncts.put(negated ? nf.formula() : nf, nf);
        }
    }

    /**
     * Adds the given formula (or its negation, depending on the value of the
     * negated flag) to this.conjuncts.
     */
    private final void addConjunct(Formula conjunct) {
        conjuncts.put(negated ? conjunct.not() : conjunct, conjunct);
    }

    /**
     * Visits the formula's children with appropriate settings for the negated flag
     * if bf has not been visited before.
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.BinaryFormula)
     */
    @Override
    public final void visit(BinaryFormula bf) {
        if (visited(bf))
            return;
        final FormulaOperator op = bf.op();
        if (op == IFF || (negated && op == AND) || (!negated && (op == OR || op == IMPLIES))) { // can't
                                                                                               // break
                                                                                               // down
                                                                                               // further
                                                                                               // in
                                                                                               // these
                                                                                               // cases
            addConjunct(bf);
        } else { // will break down further
            if (negated && op == IMPLIES) { // !(a => b) = !(!a || b) = a && !b
                negated = !negated;
                bf.left().accept(this);
                negated = !negated;
                bf.right().accept(this);
            } else {
                bf.left().accept(this);
                bf.right().accept(this);
            }
        }
    }

    /**
     * Visits the formula's children with appropriate settings for the negated flag
     * if bf has not been visited before.
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.NaryFormula)
     */
    @Override
    public final void visit(NaryFormula nf) {
        if (visited(nf))
            return;
        final FormulaOperator op = nf.op();
        if ((negated && op == AND) || (!negated && op == OR)) { // can't break
                                                               // down further
                                                               // in these
                                                               // cases
            addConjunct(nf);
        } else { // will break down further
            for (Formula f : nf) {
                f.accept(this);
            }
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visit(kodkod.ast.QuantifiedFormula)
     */
    @Override
    public final void visit(QuantifiedFormula qf) {
        if (visited(qf))
            return;

        if (breakupQuantifiers) {

            final Quantifier quant = qf.quantifier();

            if ((!negated && quant == ALL) || (negated && quant == SOME)) { // may
                                                                           // break
                                                                           // down
                                                                           // further
                final Map<Formula,Node> oldConjuncts = conjuncts;
                conjuncts = new LinkedHashMap<Formula,Node>();
                qf.formula().accept(this);
                if (conjuncts.size() > 1) { // was broken down further
                    final Decls decls = qf.decls();
                    for (Map.Entry<Formula,Node> entry : conjuncts.entrySet()) {
                        oldConjuncts.put(entry.getKey().forAll(decls), entry.getValue());
                    }
                    conjuncts = oldConjuncts;
                    return;
                } else { // wasn't broken down further
                    conjuncts = oldConjuncts;
                }
            } // won't break down further
        }

        addConjunct(qf);

    }

    /**
     * Adds f (resp. f.not()) to this.conjuncts if the negated flag is false (resp.
     * true) and the given node has not been visited; otherwise does nothing.
     *
     * @ensures !this.visited(f) => (this.conjuncts' = conjuncts + (negated =>
     *          f.not() else f)) else (this.conjuncts' = this.conjuncts)
     */
    final void visitFormula(Formula f) {
        if (visited(f))
            return;
        addConjunct(f);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(ComparisonFormula cf) {
        visitFormula(cf);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(IntComparisonFormula cf) {
        visitFormula(cf);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(MultiplicityFormula mf) {
        visitFormula(mf);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(ConstantFormula constant) {
        visitFormula(constant);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(RelationPredicate pred) {
        visitFormula(pred);
    }

}
