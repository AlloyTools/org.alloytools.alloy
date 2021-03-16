package kodkod.engine.hol;

import static kodkod.util.nodes.AnnotatedNode.annotate;

import java.util.Collection;
import java.util.HashSet;
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
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.Skolemizer;
import kodkod.engine.hol.Proc.FOL;
import kodkod.engine.hol.Proc.Fixpoint;
import kodkod.engine.hol.Proc.OR;
import kodkod.engine.hol.Proc.Some4All;
import kodkod.instance.Bounds;
import kodkod.util.nodes.AnnotatedNode;

class Conversion {

    final QuantifiedFormula origQF;
    final QuantifiedFormula newQF;

    Conversion(QuantifiedFormula origQF, QuantifiedFormula newQF) {
        this.origQF = origQF;
        this.newQF = newQF;
    }
}

/**
 * IMPORTANT: May only be applied to formulas in NNF
 */
public class HOLTranslator implements ReturnVisitor<Expression,Proc,Decls,IntExpression> {

    private final Bounds                 bounds;
    private final Options                options;
    private final AnnotatedNode<Formula> annotated;

    HOLTranslator(Bounds bounds, Options options, AnnotatedNode<Formula> annotated) {
        this.bounds = bounds;
        this.options = options;
        this.annotated = annotated;
        if (!annotated.hasHOLannotations())
            annotated.annotateHOL();
    }

    @Override
    public Decls visit(Decls decls) {
        return decls;
    }

    @Override
    public Decls visit(Decl decl) {
        return decl;
    }

    @Override
    public Expression visit(Relation relation) {
        return relation;
    }

    @Override
    public Expression visit(Variable variable) {
        return variable;
    }

    @Override
    public Expression visit(ConstantExpression constExpr) {
        return constExpr;
    }

    @Override
    public Expression visit(UnaryExpression unaryExpr) {
        return unaryExpr;
    }

    @Override
    public Expression visit(BinaryExpression binExpr) {
        return binExpr;
    }

    @Override
    public Expression visit(NaryExpression expr) {
        return expr;
    }

    @Override
    public Expression visit(IfExpression ifExpr) {
        return ifExpr;
    }

    @Override
    public Expression visit(ProjectExpression project) {
        return project;
    }

    @Override
    public Expression visit(IntToExprCast castExpr) {
        return castExpr;
    }

    @Override
    public IntExpression visit(IntConstant intConst) {
        return intConst;
    }

    @Override
    public IntExpression visit(IfIntExpression intExpr) {
        return intExpr;
    }

    @Override
    public IntExpression visit(ExprToIntCast intExpr) {
        return intExpr;
    }

    @Override
    public IntExpression visit(NaryIntExpression intExpr) {
        return intExpr;
    }

    @Override
    public IntExpression visit(BinaryIntExpression intExpr) {
        return intExpr;
    }

    @Override
    public IntExpression visit(UnaryIntExpression intExpr) {
        return intExpr;
    }

    @Override
    public IntExpression visit(SumExpression intExpr) {
        return intExpr;
    }

    @Override
    public Expression visit(Comprehension comprehension) {
        return comprehension;
    }

    @Override
    public Proc visit(IntComparisonFormula intComp) {
        return new Proc.FOL(bounds, intComp);
    }

    @Override
    public Proc visit(ConstantFormula constant) {
        return new Proc.FOL(bounds, constant);
    }

    @Override
    public Proc visit(ComparisonFormula cf) {
        return new Proc.FOL(bounds, cf);
    }

    @Override
    public Proc visit(MultiplicityFormula multFormula) {
        return new Proc.FOL(bounds, multFormula);
    }

    @Override
    public Proc visit(RelationPredicate predicate) {
        return new Proc.FOL(bounds, predicate);
    }

    @Override
    public Proc visit(NotFormula not) {
        assertNNF(not);
        return new Proc.FOL(bounds, not);
    }

    @Override
    public Proc visit(BinaryFormula binFormula) {
        if (annotated.isFOLNode(binFormula))
            return new Proc.FOL(bounds, binFormula);
        Proc left, right;
        if (binFormula.op() == FormulaOperator.OR) {
            left = toProc(binFormula.left());
            right = toProc(binFormula.right());
        } else {
            left = binFormula.left().accept(this);
            right = binFormula.right().accept(this);
        }
        return left.compose(binFormula.op(), right);
    }

    @Override
    public Proc visit(NaryFormula formula) {
        if (annotated.isFOLNode(formula))
            return new Proc.FOL(bounds, formula);
        Proc ans = null;
        for (Formula f : formula) {
            Proc p = formula.op() == FormulaOperator.OR ? toProc(f) : f.accept(this);
            ans = ans == null ? p : ans.compose(formula.op(), p);
        }
        return ans;
    }

    @Override
    public Proc visit(FixFormula fixFormula) {
        Proc fProc = toProc(fixFormula.formula());
        Proc cProc = toProc(fixFormula.condition());
        return new Proc.Fixpoint(bounds, fixFormula, fProc, cProc);
    }

    @Override
    public Proc visit(QuantifiedFormula qf) {
        assertNotSkolemizable(qf);
        Formula qfFlipped = qf.body().quantify(qf.quantifier().opposite, qf.decls(), qf.domain());
        Proc body = toProc(qfFlipped);
        boolean firstOrder = true;
        for (Decl decl : qf.decls())
            if (decl.multiplicity() != Multiplicity.ONE) {
                firstOrder = false;
                break;
            }

        if (firstOrder && body instanceof FOL && noNewHOLSkolems(((FOL) body).bounds.skolems(), bounds.skolems()))
            return new Proc.FOL(bounds, qf);
        else
            return new Proc.Some4All(bounds, qf, body);
    }

    private boolean noNewHOLSkolems(Collection<Relation> newSkolems, Collection<Relation> oldSkolems) {
        Set<Relation> diff = new HashSet<Relation>(newSkolems);
        diff.removeAll(oldSkolems);
        for (Relation sk : diff) {
            Decl d = sk.getSkolemVarDecl();
            if (d != null && d.multiplicity() != Multiplicity.ONE)
                return false;
        }
        return true;
    }

    private Proc toProc(Formula formula) {
        return HOLTranslator.toProc(AnnotatedNode.annotate(formula, annotated.sources()), bounds, options);
    }

    private void assertNotSkolemizable(QuantifiedFormula qf) {
        if (qf.quantifier() == Quantifier.SOME) {
            String msg = "It appears that the existential quantifier in '" + qf + "' is skolemizable, but it hasn't been";
            throw new IllegalStateException(msg);
        }
    }

    private void assertNNF(NotFormula not) {
        Formula f = not.formula();
        if (f instanceof BinaryFormula || f instanceof NaryFormula || f instanceof QuantifiedFormula)
            throw new IllegalStateException("Expected formula to be in NNF; got: " + not);
    }

    public static Proc toProc(Formula formula, Bounds bounds, Options options) {
        return toProc(annotate(formula), bounds, options);
    }

    public static Proc toProc(final AnnotatedNode<Formula> annotated, Bounds bounds, Options options) {
        final Bounds newBounds = bounds.clone();
        AnnotatedNode<Formula> nnf = FullNegationPropagator.toNNF(annotated, options.reporter());
        AnnotatedNode<Formula> skl = Skolemizer.skolemize(nnf, newBounds, options);
        return skl.node().accept(new HOLTranslator(newBounds, options, skl));
    }

    public static HOLTranslation proc2transl(Proc proc, Options options) {
        return proc2transl(proc, options, 0);
    }

    public static HOLTranslation proc2transl(Proc proc, Options options, int depth) {
        if (proc instanceof Proc.FOL)
            return new HOLTranslationNew.FOL((FOL) proc, options, depth);
        if (proc instanceof Proc.Some4All)
            return new HOLTranslationNew.Some4All((Some4All) proc, options, depth);
        if (proc instanceof Proc.OR)
            return new HOLTranslationNew.OR((OR) proc, options, depth);
        if (proc instanceof Proc.Fixpoint)
            return new HOLTranslationNew.Fixpoint((Fixpoint) proc, options, depth);
        throw new RuntimeException("translation not implemented for " + proc.getClass().getName());
    }

    /**
     * Don't call this for translating the top-level formula; call
     * Translator.translateHOL instead
     */
    static HOLTranslation translateHOL(Formula formula, Bounds bounds, Options options) {
        return proc2transl(toProc(annotate(formula), bounds, options), options);
    }
}
