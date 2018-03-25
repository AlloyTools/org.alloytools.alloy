package kodkod.engine.hol;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.ast.visitor.AspectReturnVisitor;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.instance.Bounds;
import kodkod.util.nodes.AnnotatedNode;

public class HOL2ProcTranslator extends AbstractReplacer {

    static class Conversion {

        final QuantifiedFormula origQF;
        final QuantifiedFormula newQF;

        Conversion(QuantifiedFormula origQF, QuantifiedFormula newQF) {
            this.origQF = origQF;
            this.newQF = newQF;
        }
    }

    class HistoryAspect extends AspectReturnVisitor<Expression,Formula,Decls,IntExpression> {

        protected HistoryAspect() {
            super(HOL2ProcTranslator.this);
        }

        @Override
        protected <T> T end(Node n, T ans) {
            stack.pop();
            skolemizable.pop();
            return ans;
        }

        @Override
        protected void start(Node n) {
            stack.push(n);
            // ***NOTE*** assumes the formula is already in NNF !!!
            boolean skolemizableSoFar = skolemizable.empty() ? true : skolemizable.lastElement();
            if (!skolemizableSoFar) {
                skolemizable.push(false);
            } else {
                if ((n instanceof BinaryFormula && ((BinaryFormula) n).op() == FormulaOperator.AND) || (n instanceof NaryFormula && ((NaryFormula) n).op() == FormulaOperator.AND) || (n instanceof QuantifiedFormula && ((QuantifiedFormula) n).quantifier() == Quantifier.SOME))
                    skolemizable.push(true);
                else
                    skolemizable.push(false);
            }
        }
    }

    protected final List<Node>       history       = new LinkedList<Node>();
    protected final Stack<Node>      stack         = new Stack<Node>();
    protected final Stack<Boolean>   skolemizable  = new Stack<Boolean>();
    protected final List<Conversion> conversions   = new ArrayList<Conversion>();
    protected final HistoryAspect    historyAspect = new HistoryAspect();

    HOL2ProcTranslator(Set<Node> cached) {
        super(cached);
        this.delegate = historyAspect;
    }

    @Override
    public Formula visit(QuantifiedFormula qf) {
        for (Decl decl : qf.decls()) {
            if (decl.multiplicity() != Multiplicity.ONE) {
                if (!isSkolemizableUpToNow())
                    throw new HigherOrderDeclException(decl);
                assert qf.decls().size() == 1 : "not implemented for quantifiers with multiple decls";
                QuantifiedFormula revQuant = (QuantifiedFormula) qf.formula().quantify(qf.quantifier().opposite, decl);
                conversions.add(new Conversion(qf, revQuant));
                return revQuant;
            }
        }
        return super.visit(qf);
    }

    public static HOLTranslation translate(AnnotatedNode<Formula> annotated, Bounds bounds, Options options) {
        HOL2ProcTranslator tr = new HOL2ProcTranslator(annotated.sharedNodes());
        Formula converted = annotated.node().accept(tr.withHistory());
        if (tr.conversions.size() == 0) {
            return new HOLTranslationOld.FOL(annotated, bounds, options);
        } else {
            return new HOLTranslationOld.Some4All(annotated, converted, tr.conversions, bounds, options);
        }
    }

    private HistoryAspect withHistory() {
        return historyAspect;
    }

    private boolean isSkolemizableUpToNow() {
        if (skolemizable.size() <= 1)
            return true;
        return skolemizable.get(skolemizable.size() - 2);
    }

}
