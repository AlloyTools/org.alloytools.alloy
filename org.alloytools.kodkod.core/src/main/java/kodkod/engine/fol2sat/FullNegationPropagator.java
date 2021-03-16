/*
 * Kodkod -- Copyright (c) 2005-2011, Emina Torlak
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
import static kodkod.ast.operator.FormulaOperator.OR;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.ConstantFormula;
import kodkod.ast.FixFormula;
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
import kodkod.engine.config.Reporter;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Propagates negations all the way down to the leafs, but without crossing
 * quantification boundaries. It also eliminates negations wherever possible
 * (e.g. double negation, !(a>b) --> a<=b, etc.) Breaks up all implications (=>)
 * and two-way implications (<=>), so that the resulting formula only contains
 * the following boolean operators: AND (&&), OR (||), and NOT (!) at the leaf
 * positions.
 */
public final class FullNegationPropagator extends AbstractVoidVisitor {

    public static AnnotatedNode<Formula> toNNF(AnnotatedNode<Formula> annotated) {
        return toNNF(annotated, null);
    }

    public static AnnotatedNode<Formula> toNNF(AnnotatedNode<Formula> annotated, Reporter reporter) {
        if (reporter != null)
            reporter.convertingToNNF();
        final FullNegationPropagator flat = new FullNegationPropagator(annotated.sharedNodes());
        annotated.node().accept(flat);
        final List<Formula> roots = new ArrayList<Formula>(flat.annotations.size());
        roots.addAll(flat.annotations.keySet());
        for (Iterator<Map.Entry<Formula,Node>> itr = flat.annotations.entrySet().iterator(); itr.hasNext();) {
            final Map.Entry<Formula,Node> entry = itr.next();
            final Node source = annotated.sourceOf(entry.getValue());
            if (entry.getKey() == source) {
                itr.remove();
                /* TODO: what is this for? */ } else {
                entry.setValue(source);
            }
        }
        return AnnotatedNode.annotate(Formula.and(flat.conjuncts), flat.annotations);
    }

    private List<Formula>     conjuncts;
    private Map<Formula,Node> annotations;
    private final Set<Node>   shared;
    private boolean           negated;
    private boolean           hasChanged;

    /**
     * Constructs a flattener for a formula in which the given nodes are shared.
     */
    private FullNegationPropagator(Set<Node> shared) {
        this(shared, new LinkedHashMap<Formula,Node>());
    }

    private FullNegationPropagator(Set<Node> shared, Map<Formula,Node> annotations) {
        this.conjuncts = new LinkedList<Formula>();
        this.annotations = annotations;
        this.shared = shared;
        this.negated = false;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.visitor.AbstractVoidVisitor#visited(kodkod.ast.Node)
     */
    @Override
    protected boolean visited(Node n) {
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

        FullNegationPropagator fne = new FullNegationPropagator(shared, annotations);
        fne.negated = !negated;
        nf.formula().accept(fne);
        if (fne.hasChanged) {
            addConjunct(Formula.and(fne.conjuncts), false, nf);
            hasChanged = true;
        } else {
            addConjunct(nf);
        }
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
        switch (op) {
            case AND :
                if (!negated) {
                    // left && right
                    bf.left().accept(this);
                    bf.right().accept(this);
                } else {
                    // !(left && right) --> !left || !right
                    FullNegationPropagator fne1 = new FullNegationPropagator(shared, annotations);
                    bf.left().not().accept(fne1);

                    FullNegationPropagator fne2 = new FullNegationPropagator(shared, annotations);
                    bf.right().not().accept(fne2);

                    addConjunct(Formula.and(fne1.conjuncts).or(Formula.and(fne2.conjuncts)), false, bf);
                    hasChanged = true;
                }
                break;
            case OR :
                if (!negated) {
                    // left || right
                    FullNegationPropagator fne1 = new FullNegationPropagator(shared, annotations);
                    bf.left().accept(fne1);

                    FullNegationPropagator fne2 = new FullNegationPropagator(shared, annotations);
                    bf.right().accept(fne2);

                    if (!fne1.hasChanged && !fne2.hasChanged) {
                        addConjunct(bf);
                    } else {
                        addConjunct(Formula.and(fne1.conjuncts).or(Formula.and(fne2.conjuncts)), false, bf);
                        hasChanged = true;
                    }
                } else {
                    // !(left || right) --> !left && !right
                    bf.left().accept(this);
                    bf.right().accept(this);
                    hasChanged = true;
                }
                break;
            case IMPLIES :
                if (!negated) {
                    // left => right --> !left || right
                    FullNegationPropagator fne1 = new FullNegationPropagator(shared, annotations);
                    bf.left().not().accept(fne1);

                    FullNegationPropagator fne2 = new FullNegationPropagator(shared, annotations);
                    bf.right().accept(fne2);

                    addConjunct(Formula.and(fne1.conjuncts).or(Formula.and(fne2.conjuncts)), false, bf);
                } else {
                    // !(left => right) --> left && !right
                    negated = false;
                    bf.left().accept(this);
                    negated = true;
                    bf.right().accept(this);
                }
                hasChanged = true;
                break;
            case IFF :
                FullNegationPropagator fne1 = new FullNegationPropagator(shared, annotations);
                FullNegationPropagator fne2 = new FullNegationPropagator(shared, annotations);
                if (!negated) {
                    // a <=> b --> (a && b) || (!a && !b)
                    bf.left().and(bf.right()).accept(fne1);
                    bf.left().not().and(bf.right().not()).accept(fne2);
                } else {
                    // !(a = b) --> (a && !b) || (!a && b)
                    Formula orLhs = bf.left().and(bf.right().not());
                    orLhs.accept(fne1);
                    Formula orRhs = bf.left().not().and(bf.right());
                    orRhs.accept(fne2);
                }
                addConjunct(Formula.and(fne1.conjuncts).or(Formula.and(fne2.conjuncts)), false, bf);
                hasChanged = true;
                break;
            default :
                addConjunct(bf);
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
        if (negated && op == AND) {
            List<Formula> formulas = new LinkedList<Formula>();
            for (Formula f : nf) {
                FullNegationPropagator fne = new FullNegationPropagator(shared, annotations);
                f.not().accept(fne);
                formulas.add(Formula.and(fne.conjuncts));
            }
            addConjunct(Formula.or(formulas), false, nf);
            hasChanged = true;
        } else if (!negated && op == OR) {
            List<Formula> formulas = new LinkedList<Formula>();
            boolean changed = false;
            for (Formula f : nf) {
                FullNegationPropagator fne = new FullNegationPropagator(shared, annotations);
                f.accept(fne);
                changed = changed || fne.hasChanged;
                formulas.add(Formula.and(fne.conjuncts));
            }
            if (changed) {
                addConjunct(Formula.or(formulas), false, nf);
                hasChanged = true;
            } else {
                addConjunct(nf);
            }
        } else {
            for (Formula f : nf) {
                f.accept(this);
            }
            hasChanged = negated;
        }
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

    @Override
    public final void visit(QuantifiedFormula qf) {
        if (visited(qf))
            return;
        FullNegationPropagator fneBody = new FullNegationPropagator(shared, annotations);
        fneBody.negated = negated;
        boolean wasNegated = negated;
        negated = false;
        qf.body().accept(fneBody);

        FullNegationPropagator fneDomain = new FullNegationPropagator(shared, annotations);
        qf.domain().accept(fneDomain);

        if (fneBody.hasChanged || fneDomain.hasChanged || wasNegated) {
            Formula qfBody = Formula.and(fneBody.conjuncts);
            Quantifier quant = wasNegated ? qf.quantifier().opposite : qf.quantifier();
            addConjunct(qfBody.quantify(quant, qf.decls(), Formula.and(fneDomain.conjuncts)), false, qf);
            hasChanged = true;
        } else {
            addConjunct(qf);
        }
        negated = wasNegated;
    }

    @Override
    public final void visit(FixFormula qf) {
        addConjunct(qf);
        // if (visited(qf)) return;
        // if (!negated) {
        // addConjunct(qf, false, qf);
        // } else {
        // negated = false;
        // qf.formula().accept(this);
        // hasChanged = true;
        // negated = true;
        // }
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(ComparisonFormula cf) {
        visitFormula(cf);
    }

    /** @see #visitFormula(Formula) */
    @Override
    public final void visit(IntComparisonFormula cf) {
        if (visited(cf))
            return;
        if (!negated) {
            addConjunct(cf);
        } else {
            switch (cf.op()) {
                case GT :
                    addConjunct(cf.left().lte(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                case GTE :
                    addConjunct(cf.left().lt(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                case LT :
                    addConjunct(cf.left().gte(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                case LTE :
                    addConjunct(cf.left().gt(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                case EQ :
                    addConjunct(cf.left().neq(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                case NEQ :
                    addConjunct(cf.left().eq(cf.right()), false, cf);
                    hasChanged = true;
                    break;
                default :
                    addConjunct(cf);
            }
        }
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

    /**
     * Adds the given formula (or its negation, depending on the value of the
     * negated flag) to this.conjuncts.
     */
    private final void addConjunct(Formula conjunct) {
        addConjunct(conjunct, negated, conjunct);
    }

    private final void addConjunct(Formula conjunct, boolean neg, Node source) {
        Formula f = neg ? not(conjunct) : conjunct;
        conjuncts.add(f);
        annotations.put(f, source);
    }

    private Formula not(Formula f) {
        return f instanceof NotFormula ? ((NotFormula) f).formula() : f.not();
    }

}
