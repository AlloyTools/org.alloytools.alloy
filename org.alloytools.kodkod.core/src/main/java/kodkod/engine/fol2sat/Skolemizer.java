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
import static kodkod.util.nodes.AnnotatedNode.annotate;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntExpression;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Skolemizes existential quantifiers, up to a given number of nestings (within
 * universal quantifiers).
 *
 * @author Emina Torlak
 */
public abstract class Skolemizer extends AbstractReplacer {

    /**
     * Skolemizes the given annotated formula using the given bounds and options. If
     * Options.logTranslation is set and the formula is skolemizable, the resulting
     * annotated formula will contain transitive source information for each of its
     * subformulas. Specifically, let f be the returned annotated formula, t be a
     * descendant of f.node, and s a descendant of annotated.node from which t was
     * derived. Then, f.source[t] = annotated.source[s]. If options.logTranslation
     * is false, no source information will be recorded (i.e. f.source[t] = t for
     * all descendants t of f).
     *
     * @ensures upper bound mappings for skolem constants, if any, are added to the
     *          bounds
     * @return the skolemized version of the given formula
     * @throws NullPointerException any of the arguments are null
     * @throws IllegalArgumentException some Relation & annotated.node.^children -
     *             bounds.relations
     * @throws UnsupportedOperationException bounds is unmodifiable
     */
    public static AnnotatedNode<Formula> skolemize(final AnnotatedNode<Formula> annotated, Bounds bounds, Options options) {
        if (options.logTranslation() > 0) {
            final Map<Node,Node> source = new IdentityHashMap<Node,Node>();
            final Skolemizer r = new Skolemizer(annotated, bounds, options) {

                @Override
                protected Formula source(Formula f, Node n) {
                    // System.out.println("logging " + f + " <-- " + n);
                    final Node nsource = annotated.sourceOf(n);
                    if (f != nsource)
                        source.put(f, nsource);
                    return f;
                }
            };
            final Formula f = annotated.node().accept(r);
            return f == annotated.node() ? annotated : annotate(f, source);
        } else {
            final Skolemizer r = new Skolemizer(annotated, bounds, options) {};
            final Formula f = annotated.node().accept(r);
            return f == annotated.node() ? annotated : annotate(f);
        }
    }

    /**
     * Contains info about an approximate bound for a non-skolemizable decl.
     *
     * @specfield decl: Decl
     * @specfield upperBound: lone BooleanMatrix
     * @invariant decl.expression in upperBound
     * @author Emina Torlak
     */
    private static final class DeclInfo {

        final Decl    decl;
        BooleanMatrix upperBound;

        /**
         * Constructs a DeclInfo for the given decl.
         *
         * @ensures this.decl' = decl && this.upperBound' = null
         */
        DeclInfo(Decl decl) {
            this.decl = decl;
            this.upperBound = null;
        }
    }

    /*
     * replacement environment; maps skolemized variables to their skolem
     * expressions, and non-skolemized variables to themselves
     */
    private Environment<Expression,Expression> repEnv;
    /*
     * the interpreter used to determine the upper bounds for skolem constants; the
     * upper bounds for skolem constants will be added to interpreter.bounds
     */
    private final LeafInterpreter              interpreter;
    /* bounds on which the interpreter is based */
    private final Bounds                       bounds;
    /* reporter */
    private final Reporter                     reporter;
    /*
     * non-skolemizable quantified declarations in the current scope, in the order
     * of declaration (most recent decl is last in the list)
     */
    private final List<DeclInfo>               nonSkolems;
    /* a Decl-only view of the nonSkolems list */
    private final List<Decl>                   nonSkolemsView;
    private final List<Formula>                topSkolemConstraints;
    /*
     * true if the polarity of the currently visited node is negative, otherwise
     * false
     */
    private boolean                            negated;
    /*
     * depth to which to skolemize; negative depth indicates that no skolemization
     * can be done at that point
     */
    private int                                skolemDepth;

    /**
     * Constructs a skolem replacer from the given arguments.
     */
    private Skolemizer(AnnotatedNode<Formula> annotated, Bounds bounds, Options options) {
        super(annotated.sharedNodes());

        // only cache intermediate computations for expressions with no free
        // variables
        // and formulas with no free variables and no quantified descendents
        for (Node n : annotated.sharedNodes()) {
            final AbstractDetector fvdetect = annotated.freeVariableDetector();
            final AbstractDetector qdetect = annotated.quantifiedFormulaDetector();
            if (!(Boolean) n.accept(fvdetect)) {
                if (!(n instanceof Formula) || !((Boolean) n.accept(qdetect)))
                    this.cache.put(n, null);
            }
        }
        this.reporter = options.reporter();
        this.bounds = bounds;
        this.interpreter = LeafInterpreter.overapproximating(bounds, options);
        this.repEnv = Environment.empty();
        this.nonSkolems = new ArrayList<DeclInfo>();
        this.nonSkolemsView = new AbstractList<Decl>() {

            @Override
            public Decl get(int index) {
                return nonSkolems.get(index).decl;
            }

            @Override
            public int size() {
                return nonSkolems.size();
            }
        };
        this.topSkolemConstraints = new ArrayList<Formula>();
        this.negated = false;
        this.skolemDepth = options.skolemDepth();
    }

    /**
     * Caches the given replacement for the specified node, if the node is a
     * syntactically shared expression, int expression or declaration with no free
     * variables. Otherwise does nothing. The method returns the replacement node.
     *
     * @return replacement
     */
    @Override
    protected final <N extends Node> N cache(N node, N replacement) {
        if (cache.containsKey(node)) {
            cache.put(node, replacement);
        }
        return replacement;
    }

    /**
     * Records that the given node is the source of the specified formula, if this
     * is a tracking skolemizer. Otherwise does nothing. This method is always
     * called when the result of visiting a node n will result in the creation of a
     * formula f such that f != n.
     *
     * @return f
     * @ensures Records that the given node is the source of the specified formula,
     *          if this is a tracking skolemizer. Otherwise does nothing.
     */
    protected Formula source(Formula f, Node n) {
        return f;
    }

    /*-------declarations---------*/
    /**
     * Visits the given decl's expression. Note that we must not visit variables in
     * case they are re-used. For example, consider the formula some x: X | all x: Y
     * | F(x). Since x bound by the existential quantifier is going to be
     * skolemized, if we visited the variable in the enclosed declaration, we would
     * get the skolem constant as a return value and a ClassCastException would be
     * thrown.
     *
     * @return { d: Declaration | d.variable = decl.variable && d.multiplicity =
     *         decl.multiplicity && d.expression = decl.expression.accept(this) }
     */
    @Override
    public final Decl visit(Decl decl) {
        Decl ret = lookup(decl);
        if (ret != null)
            return ret;
        final int oldDepth = skolemDepth;
        skolemDepth = -1; // can't skolemize inside a decl
        final Expression expression = decl.expression().accept(this);
        skolemDepth = oldDepth;
        ret = (expression == decl.expression()) ? decl : decl.variable().declare(decl.multiplicity(), expression);
        return cache(decl, ret);
    }

    /**
     * This method should be accessed only from the context of a non-skolemizable
     * node, because it extends the replacement environment with identity mappings
     * for the variables declared in the given decls. To ensure that the environment
     * is always extended, the method should be called using the visit((Decls)
     * node.declarations()) syntax, since the accept syntax may dynamically dispatch
     * the call to the {@link #visit(Decl)} method, producing UnboundLeafExceptions.
     *
     * @ensures this.repEnv in this.repEnv'.^parent && #(this.repEnv'.*parent -
     *          this.repEnv.*parent) = decls.size() && all v: decls.variable |
     *          this.repEnv'.lookup(v) = v
     * @requires this.skolemDepth < 0
     * @return { d: Decls | d.size = decls.size && all i: [0..d.size) |
     *         d.declarations[i] = decls.declarations[i].accept(this) }
     */
    @Override
    public final Decls visit(Decls decls) {
        Decls ret = lookup(decls);
        if (ret == null) {
            Decls visitedDecls = null;
            boolean allSame = true;
            for (Decl decl : decls) {
                Decls newDecl = visit(decl);
                if (newDecl != decl)
                    allSame = false;
                visitedDecls = (visitedDecls == null) ? newDecl : visitedDecls.and(newDecl);
                repEnv = repEnv.extend(decl.variable(), decl.expression(), decl.variable());
            }
            ret = allSame ? decls : visitedDecls;
            return cache(decls, ret);
        } else { // just extend the replacement environment
            for (Decl decl : decls) {
                repEnv = repEnv.extend(decl.variable(), decl.expression(), decl.variable());
            }
            return ret;
        }
    }

    /*-------expressions and intexpressions---------*/
    /*
     * INVARIANT: whenever an expression or intexpression is visited, skolemDepth <
     * 0
     */
    /**
     * Returns the binding for the given variable in the current replacement
     * environment.
     *
     * @return the binding for the given variable in the current replacement
     *         environment.
     * @throws UnboundLeafException variable not bound in teh replacement
     *             environment.
     */
    @Override
    public final Expression visit(Variable variable) {
        final Expression ret = repEnv.lookup(variable);
        if (ret == null)
            throw new UnboundLeafException("Unbound variable", variable);
        return ret;
    }

    /**
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.Comprehension)
     */
    @Override
    public final Expression visit(Comprehension expr) {
        Expression ret = lookup(expr);
        if (ret != null)
            return ret;
        final Environment<Expression,Expression> oldRepEnv = repEnv; // skolemDepth
                                                                    // < 0
                                                                    // at
                                                                    // this
                                                                    // point
        final Decls decls = visit(expr.decls());
        final Formula formula = expr.formula().accept(this);
        ret = (decls == expr.decls() && formula == expr.formula()) ? expr : formula.comprehension(decls);
        repEnv = oldRepEnv;
        return cache(expr, ret);
    }

    /**
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.SumExpression)
     */
    @Override
    public final IntExpression visit(SumExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;
        final Environment<Expression,Expression> oldRepEnv = repEnv; // skolemDepth
                                                                    // < 0
                                                                    // at
                                                                    // this
                                                                    // point
        final Decls decls = visit(intExpr.decls());
        final IntExpression expr = intExpr.intExpr().accept(this);
        ret = (decls == intExpr.decls() && expr == intExpr.intExpr()) ? intExpr : expr.sum(decls);
        repEnv = oldRepEnv;
        return cache(intExpr, ret);
    }

    /*-------formulas---------*/
    /**
     * Returns the least sound upper bound on the value of expr
     *
     * @return the least sound upper bound on the value of expr
     */
    private final BooleanMatrix upperBound(Expression expr, Environment<BooleanMatrix,Expression> env) {
        return FOL2BoolTranslator.approximate(annotate(expr), interpreter, env);
    }

    /**
     * Adds a bound for the given skolem relation to this.bounds, and returns the
     * expression that should replace skolemDecl.variable in the final formula.
     *
     * @requires skolem !in this.bounds.relations
     * @requires skolem.arity = nonSkolems.size() + skolemDecl.variable().arity()
     * @ensures adds a sound upper bound for the given skolem relation to
     *          this.bounds
     * @return the expression that should replace skolemDecl.variable in the final
     *         formula
     */
    private Expression skolemExpr(Decl skolemDecl, Relation skolem) {
        final int depth = nonSkolems.size();
        final int arity = depth + skolemDecl.variable().arity();

        Expression skolemExpr = skolem;
        Environment<BooleanMatrix,Expression> skolemEnv = Environment.empty();

        for (DeclInfo info : nonSkolems) {
            if (info.upperBound == null) {
                info.upperBound = upperBound(info.decl.expression(), skolemEnv);
            }
            skolemEnv = skolemEnv.extend(info.decl.variable(), info.decl.expression(), info.upperBound);
            skolemExpr = info.decl.variable().join(skolemExpr);
        }

        BooleanMatrix matrixBound = upperBound(skolemDecl.expression(), skolemEnv);
        for (int i = depth - 1; i >= 0; i--) {
            matrixBound = nonSkolems.get(i).upperBound.cross(matrixBound);
        }

        final TupleSet skolemBound = bounds.universe().factory().setOf(arity, matrixBound.denseIndices());
        bounds.bound(skolem, skolemBound);

        return skolemExpr;
    }

    /**
     * Returns a formula that properly constrains the given skolem's domain.
     *
     * @requires !nonSkolems.isEmpty()
     * @return a formula that properly constrains the given skolem's domain.
     */
    private Formula domainConstraint(Decl skolemDecl, Relation skolem) {
        final Iterator<DeclInfo> itr = nonSkolems.iterator();
        Decls rangeDecls = null;
        while (itr.hasNext()) {
            Decl d = itr.next().decl;
            Decl dd = d.variable().oneOf(d.expression());
            rangeDecls = rangeDecls != null ? rangeDecls.and(dd) : dd;
        }
        // System.out.println(skolemDecl.expression());
        Expression skolemDomain = skolem;
        for (int i = 0, max = skolemDecl.variable().arity(); i < max; i++) {
            skolemDomain = skolemDomain.join(Expression.UNIV);
        }
        return skolemDomain.in(Formula.TRUE.comprehension(rangeDecls));
    }

    /**
     * Skolemizes the given formula, if possible, otherwise returns the result of
     * replacing its free variables according to the current replacement
     * environment.
     *
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.QuantifiedFormula)
     */
    @Override
    public final Formula visit(QuantifiedFormula qf) {
        Formula ret = lookup(qf);
        if (ret != null)
            return ret;

        final Environment<Expression,Expression> oldRepEnv = repEnv;
        final Quantifier quant = qf.quantifier();
        final Decls decls = qf.decls();

        if (skolemDepth >= 0 && (negated && quant == ALL || !negated && quant == SOME)) { // skolemizable
                                                                                         // formula
            final List<Formula> rangeConstraints = new LinkedList<Formula>();
            final List<Formula> domConstraints = new LinkedList<Formula>();

            for (Decl decl : decls) {
                final Decl skolemDecl = visit(decl);

                Variable skVar = skolemDecl.variable();
                final Relation skolem = Relation.skolem("$" + skVar.name(), nonSkolems.size() + skVar.arity(), skVar, skolemDecl, quant);
                reporter.skolemizing(decl, skolem, nonSkolemsView);

                final Expression skolemExpr = skolemExpr(skolemDecl, skolem);

                final Multiplicity mult = decl.multiplicity();
                rangeConstraints.add(source(skolemExpr.in(skolemDecl.expression()), decl));
                if (mult != Multiplicity.SET) {
                    rangeConstraints.add(source(skolemExpr.apply(mult), decl));
                }

                if (!nonSkolems.isEmpty())
                    domConstraints.add(source(domainConstraint(skolemDecl, skolem), decl));

                repEnv = repEnv.extend(decl.variable(), decl.expression(), skolemExpr);
            }

            ret = source(Formula.and(rangeConstraints), decls).compose(negated ? IMPLIES : AND, qf.formula().accept(this));

            if (!domConstraints.isEmpty())
                topSkolemConstraints.add(source(Formula.and(domConstraints), decls));

        } else { // non-skolemizable formula

            final Decls newDecls = visit(qf.decls());
            if (skolemDepth >= nonSkolems.size() + newDecls.size()) { // could
                                                                     // skolemize
                                                                     // below
                for (Decl d : newDecls) {
                    nonSkolems.add(new DeclInfo(d));
                }
                final Formula domain = qf.domain().accept(this);
                final Formula body = qf.body().accept(this);
                ret = ((newDecls == decls && domain == qf.domain() && body == qf.body()) ? qf : body.quantify(quant, newDecls, domain));
                for (int i = newDecls.size(); i > 0; i--) {
                    nonSkolems.remove(nonSkolems.size() - 1);
                }
            } else { // can't skolemize below
                final int oldDepth = skolemDepth;
                skolemDepth = -1;
                final Formula domain = qf.domain().accept(this);
                final Formula body = qf.body().accept(this);
                ret = ((newDecls == decls && domain == qf.domain() && body == qf.body()) ? qf : body.quantify(quant, newDecls, domain));
                skolemDepth = oldDepth;
            }
        }

        repEnv = oldRepEnv;
        if (repEnv.isEmpty() && !topSkolemConstraints.isEmpty()) {
            ret = source(Formula.and(topSkolemConstraints), qf).compose(negated ? IMPLIES : AND, ret);
        }
        return source(cache(qf, ret), qf);
    }

    /**
     * Calls not.formula.accept(this) after flipping the negation flag and returns
     * the result.
     *
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.NotFormula)
     **/
    @Override
    public final Formula visit(NotFormula not) {
        Formula ret = lookup(not);
        if (ret != null)
            return ret;
        negated = !negated; // flip the negation flag
        final Formula retChild = not.formula().accept(this);
        negated = !negated;
        return retChild == not.formula() ? cache(not, not) : source(cache(not, retChild.not()), not);
    }

    /**
     * If not cached, visits the formula's children with appropriate settings for
     * the negated flag and the skolemDepth parameter.
     *
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.BinaryFormula)
     */
    @Override
    public final Formula visit(BinaryFormula bf) {
        Formula ret = lookup(bf);
        if (ret != null)
            return ret;
        final FormulaOperator op = bf.op();
        final int oldDepth = skolemDepth;
        if (op == IFF || (negated && op == AND) || (!negated && (op == OR || op == IMPLIES))) { // cannot
                                                                                               // skolemize
                                                                                               // in
                                                                                               // these
                                                                                               // cases
            skolemDepth = -1;
        }
        final Formula left, right;
        if (negated && op == IMPLIES) { // !(a => b) = !(!a || b) = a && !b
            negated = !negated;
            left = bf.left().accept(this);
            negated = !negated;
            right = bf.right().accept(this);
        } else {
            left = bf.left().accept(this);
            right = bf.right().accept(this);
        }
        skolemDepth = oldDepth;
        ret = (left == bf.left() && right == bf.right()) ? bf : left.compose(op, right);
        return source(cache(bf, ret), bf);
    }

    /**
     * If not cached, visits the formula's children with appropriate settings for
     * the negated flag and the skolemDepth parameter.
     *
     * @see kodkod.ast.visitor.AbstractReplacer#visit(kodkod.ast.NaryFormula)
     */
    @Override
    public final Formula visit(NaryFormula bf) {
        Formula ret = lookup(bf);
        if (ret != null)
            return ret;

        final int oldDepth = skolemDepth;
        final FormulaOperator op = bf.op();

        switch (op) {
            case AND :
                if (negated)
                    skolemDepth = -1;
                break;
            case OR :
                if (!negated)
                    skolemDepth = -1;
                break;
            default :
                throw new IllegalArgumentException("Unknown nary operator: " + op);
        }

        final Formula[] visited = new Formula[bf.size()];
        boolean allSame = true;
        for (int i = 0; i < visited.length; i++) {
            final Formula child = bf.child(i);
            visited[i] = child.accept(this);
            allSame = allSame && (child == visited[i]);
        }
        ret = allSame ? bf : Formula.compose(op, visited);

        skolemDepth = oldDepth;

        return source(cache(bf, ret), bf);
    }

    /**
     * Calls super.visit(icf) after disabling skolemization and returns the result.
     *
     * @return super.visit(icf)
     **/
    @Override
    public final Formula visit(IntComparisonFormula icf) {
        final int oldDepth = skolemDepth;
        skolemDepth = -1; // cannot skolemize inside an int comparison formula
        final Formula ret = super.visit(icf);
        skolemDepth = oldDepth;
        return source(ret, icf);
    }

    /**
     * Calls super.visit(cf) after disabling skolemization and returns the result.
     *
     * @return super.visit(cf)
     **/
    @Override
    public final Formula visit(ComparisonFormula cf) {
        final int oldDepth = skolemDepth;
        skolemDepth = -1; // cannot skolemize inside a comparison formula
        final Formula ret = super.visit(cf);
        skolemDepth = oldDepth;
        return source(ret, cf);
    }

    /**
     * Calls super.visit(mf) after disabling skolemization and returns the result.
     *
     * @return super.visit(mf)
     **/
    @Override
    public final Formula visit(MultiplicityFormula mf) {
        final int oldDepth = skolemDepth;
        skolemDepth = -1; // cannot skolemize inside a multiplicity formula
        final Formula ret = super.visit(mf);
        skolemDepth = oldDepth;
        return source(ret, mf);
    }

    /**
     * Calls super.visit(pred) after disabling skolemization and returns the result.
     *
     * @return super.visit(pred)
     **/
    @Override
    public final Formula visit(RelationPredicate pred) {
        final int oldDepth = skolemDepth;
        skolemDepth = -1; // cannot skolemize inside a relation predicate
        final Formula ret = super.visit(pred);
        skolemDepth = oldDepth;
        return source(ret, pred);
    }
}
