package kodkod.engine.fol2sat;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.util.nodes.AnnotatedNode;
import kodkod.util.nodes.Nodes;

/*
 * TODO:
 * what if we have something like
 *
 *   some N &&
 *   all n: N | ...
 *
 * That is not necessarily equisatisfiable to
 *
 *   all n: N |
 *     some N &&
 *     ...
 *
 * Potential solution:
 *   check that there are no constraints on quantification domains
 */
public class PrenexNFConverter extends AbstractReplacer {

    public static AnnotatedNode<Formula> toPNF(AnnotatedNode<Formula> annotated) {
        final PrenexNFConverter pnfConv = new PrenexNFConverter(annotated.sharedNodes());
        List<Formula> conj = new ArrayList<Formula>();
        for (Formula f : Nodes.allConjuncts(annotated.node(), null))
            conj.add(f.accept(pnfConv));
        Formula ans = Formula.and(conj);

        final List<Formula> roots = new ArrayList<Formula>(pnfConv.annotations.size());
        roots.addAll(pnfConv.annotations.keySet());
        for (Iterator<Map.Entry<Formula,Node>> itr = pnfConv.annotations.entrySet().iterator(); itr.hasNext();) {
            final Map.Entry<Formula,Node> entry = itr.next();
            final Node source = annotated.sourceOf(entry.getValue());
            if (entry.getKey() == source) {
                itr.remove();
            } else {
                entry.setValue(source);
            }
        }

        return AnnotatedNode.annotate(ans, pnfConv.annotations);
    }

    private Map<Formula,Node> annotations;

    public PrenexNFConverter(Set<Node> shared) {
        super(shared, new IdentityHashMap<Node,Node>());
        this.annotations = new LinkedHashMap<Formula,Node>();
    }

    @Override
    public Formula visit(BinaryFormula bf) {
        Formula ans;
        switch (bf.op()) {
            case AND :
            case OR :
                Formula left = bf.left().accept(this);
                Formula right = bf.right().accept(this);
                Pair p = new Pair(left, right);
                if (p.hasNoQuant() && left == bf.left() && right == bf.right())
                    ans = bf;
                else
                    ans = p.compose(bf.op());
                break;
            case IMPLIES :
                ans = bf.left().not().or(bf.right()).accept(this);
                break;
            case IFF :
                ans = bf.left().and(bf.right()).or(bf.left().not().and(bf.right().not())).accept(this);
                break;
            default :
                throw new IllegalStateException("Unknown BinaryFormula operator: " + bf.op());
        }
        return saveMapping(ans, bf);
    }

    @Override
    public Formula visit(NotFormula not) {
        Formula sub = not.formula().accept(this);
        Pair p = new Pair(sub, null);
        Formula ans;
        if (p.hasNoQuant() && sub == not.formula())
            ans = not;
        else if (p.hasNoQuant())
            ans = sub.not();
        else
            ans = pushNegation(p.leftQF);
        return saveMapping(ans, not);
    }

    @Override
    public Formula visit(NaryFormula formula) {
        final ArrayList<Formula> children = new ArrayList<Formula>(formula.size());
        boolean allSame = true;
        boolean noQuant = true;
        for (Formula ch : formula) {
            Formula ch2 = ch.accept(this);
            allSame = allSame && ch == ch2;
            noQuant = noQuant && !(ch2 instanceof QuantifiedFormula);
            children.add(ch2);
        }
        Formula ans;
        if (allSame && noQuant) {
            ans = formula;
        } else {
            ans = children.get(0);
            for (int i = 1; i < children.size(); i++)
                ans = new Pair(ans, children.get(i)).compose(formula.op());
        }
        return saveMapping(ans, formula);
    }

    protected Formula pushNegation(QuantifiedFormula f) {
        return pushNegation(f.formula()).quantify(f.quantifier().opposite, f.decls());
    }

    protected Formula pushNegation(Formula f) {
        if (f instanceof QuantifiedFormula)
            return pushNegation((QuantifiedFormula) f);
        return f.not();
    }

    protected Formula saveMapping(Formula f, Node source) {
        annotations.put(f, source);
        return f;
    }

    class Pair {

        public final Formula           left;
        public final QuantifiedFormula leftQF;
        public final Formula           right;
        public final QuantifiedFormula rightQF;

        Pair(Formula left, Formula right) {
            this.left = left;
            this.leftQF = (left instanceof QuantifiedFormula) ? (QuantifiedFormula) left : null;
            this.right = right;
            this.rightQF = (right instanceof QuantifiedFormula) ? (QuantifiedFormula) right : null;
        }

        boolean hasNoQuant() {
            return leftQF == null && rightQF == null;
        }

        Formula compose(FormulaOperator op) {
            if (leftQF == null && rightQF == null) {
                return left.compose(op, right);
            } else if (leftQF != null && rightQF != null) {
                // TODO do var renaming
                QuantifiedFormula l = leftQF, r = rightQF;
                if (r.decls().get(0).multiplicity() == Multiplicity.SET && l.decls().get(0).multiplicity() != Multiplicity.SET) {
                    l = rightQF;
                    r = leftQF;
                }
                Formula newBody = l.formula().compose(op, r.formula());
                return newBody.quantify(r.quantifier(), r.decls()).quantify(l.quantifier(), l.decls());
            } else {
                // TODO do var renaming
                QuantifiedFormula qf = leftQF != null ? leftQF : rightQF;
                // Formula other = leftQF != null ? right: left;
                // TODO: check that other doesn't constraint qf.decls.expression
                Formula leftBody = leftQF != null ? leftQF.formula() : left;
                Formula rightBody = rightQF != null ? rightQF.formula() : right;
                Formula newBody = new Pair(leftBody, rightBody).compose(op);
                return newBody.quantify(qf.quantifier(), qf.decls());
            }
        }
    }

}
