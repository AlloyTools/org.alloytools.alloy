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
package kodkod.ast.visitor;

import java.util.IdentityHashMap;
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
import kodkod.ast.operator.Multiplicity;

/**
 * A depth first replacer. The default implementation returns the tree to which
 * it is applied. Reference equality is used to determine if two nodes are the
 * same.
 *
 * @specfield cached: set Node // result of visiting these nodes will be cached
 * @specfield cache: Node ->lone Node
 * @invariant cached in cache.Node
 * @author Emina Torlak
 */
public abstract class AbstractReplacer implements ReturnVisitor<Expression,Formula,Decls,IntExpression> {

    protected final Map<Node,Node>                                  cache;
    protected final Set<Node>                                       cached;
    protected ReturnVisitor<Expression,Formula,Decls,IntExpression> delegate;

    /**
     * Constructs a depth-first replaces which will cache the results of visiting
     * the given nodes and re-use them on subsequent visits.
     *
     * @ensures this.cached' = cached && no this.cache'
     */
    protected AbstractReplacer(Set<Node> cached) {
        this(cached, new IdentityHashMap<Node,Node>(cached.size()), null);
    }

    protected AbstractReplacer(Set<Node> cached, ReturnVisitor<Expression,Formula,Decls,IntExpression> delegate) {
        this(cached, new IdentityHashMap<Node,Node>(cached.size()), delegate);
    }

    protected AbstractReplacer(Set<Node> cached, Map<Node,Node> cache) {
        this(cached, cache, null);
    }

    /**
     * Constructs a depth-first replacer which will cache the results of visiting
     * the given nodes in the given map, and re-use them on subsequent visits.
     *
     * @param delegate
     * @ensures this.cached' = cached && this.cache' = cache
     */
    protected AbstractReplacer(Set<Node> cached, Map<Node,Node> cache, ReturnVisitor<Expression,Formula,Decls,IntExpression> delegate) {
        this.cached = cached;
        this.cache = cache;
        this.delegate = delegate == null ? this : delegate;
    }

    /**
     * If the given node has already been visited and its replacement cached, the
     * cached value is returned. Otherwise, null is returned.
     *
     * @return this.cache[node]
     */
    @SuppressWarnings("unchecked" )
    protected <N extends Node> N lookup(N node) {
        return (N) cache.get(node);
    }

    /**
     * Caches the given replacement for the specified node, if this is a caching
     * visitor. Otherwise does nothing. The method returns the replacement node.
     *
     * @ensures node in this.cached => this.cache' = this.cache ++
     *          node->replacement, this.cache' = this.cache
     * @return replacement
     */
    protected <N extends Node> N cache(N node, N replacement) {
        if (cached.contains(node)) {
            cache.put(node, replacement);
        }
        return replacement;
    }

    /**
     * Calls lookup(decls) and returns the cached value, if any. If a replacement
     * has not been cached, visits each of the children's variable and expression.
     * If nothing changes, the argument is cached and returned, otherwise a
     * replacement Decls object is cached and returned.
     *
     * @return { d: Decls | d.size = decls.size && all i: [0..d.size) |
     *         d.declarations[i] = decls.declarations[i].accept(delegate) }
     */
    @Override
    public Decls visit(Decls decls) {
        Decls ret = lookup(decls);
        if (ret != null)
            return ret;

        Decls visitedDecls = null;
        boolean allSame = true;
        for (Decl decl : decls) {
            Decls newDecl = visit(decl);
            if (newDecl != decl)
                allSame = false;
            visitedDecls = (visitedDecls == null) ? newDecl : visitedDecls.and(newDecl);
        }
        ret = allSame ? decls : visitedDecls;
        return cache(decls, ret);
    }

    /**
     * Calls lookup(decl) and returns the cached value, if any. If a replacement has
     * not been cached, visits the declaration's variable and expression. If nothing
     * changes, the argument is cached and returned, otherwise a replacement Decl
     * object is cached and returned.
     *
     * @return { d: Declaration | d.variable = declaration.variable.accept(delegate)
     *         && d.multiplicity = decl.multiplicity && d.expression =
     *         declaration.expression.accept(delegate)
     */
    @Override
    public Decl visit(Decl decl) {
        Decl ret = lookup(decl);
        if (ret != null)
            return ret;

        final Variable variable = (Variable) decl.variable().accept(delegate);
        final Expression expression = decl.expression().accept(delegate);
        ret = (variable == decl.variable() && expression == decl.expression()) ? decl : variable.declare(decl.multiplicity(), expression);
        return cache(decl, ret);
    }

    /**
     * Calls lookup(relation) and returns the cached value, if any. If a replacement
     * has not been cached, the relation is cached and returned.
     *
     * @return relation
     */
    @Override
    public Expression visit(Relation relation) {
        final Expression ret = lookup(relation);
        return ret == null ? cache(relation, relation) : ret;
    }

    /**
     * Calls lookup(variable) and returns the cached value, if any. If a replacement
     * has not been cached, the variable is cached and returned.
     *
     * @return variable
     */
    @Override
    public Expression visit(Variable variable) {
        final Expression ret = lookup(variable);
        return ret == null ? cache(variable, variable) : variable;
    }

    /**
     * Calls lookup(constExpr) and returns the cached value, if any. If a
     * replacement has not been cached, the constExpr is cached and returned.
     *
     * @return constExpr
     */
    @Override
    public Expression visit(ConstantExpression constExpr) {
        final Expression ret = lookup(constExpr);
        return ret == null ? cache(constExpr, constExpr) : constExpr;
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If a replacement has
     * not been cached, visits the expr's children. If nothing changes, the argument
     * is cached and returned, otherwise a replacement expr is cached and returned.
     *
     * @return { e: Expression | e.op = expr.op && #e.children = #expr.children &&
     *         all i: [0..expr.children) | e.child(i) =
     *         expr.child(i).accept(delegate) }
     */
    @Override
    public Expression visit(NaryExpression expr) {
        Expression ret = lookup(expr);
        if (ret != null)
            return ret;

        final Expression[] visited = new Expression[expr.size()];
        boolean allSame = true;
        for (int i = 0; i < visited.length; i++) {
            final Expression child = expr.child(i);
            visited[i] = child.accept(delegate);
            allSame = allSame && visited[i] == child;
        }

        ret = allSame ? expr : Expression.compose(expr.op(), visited);
        return cache(expr, ret);
    }

    /**
     * Calls lookup(binExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's children. If nothing changes,
     * the argument is cached and returned, otherwise a replacement expression is
     * cached and returned.
     *
     * @return { b: BinaryExpression | b.left = binExpr.left.accept(delegate) &&
     *         b.right = binExpr.right.accept(delegate) && b.op = binExpr.op }
     */
    @Override
    public Expression visit(BinaryExpression binExpr) {
        Expression ret = lookup(binExpr);
        if (ret != null)
            return ret;

        final Expression left = binExpr.left().accept(delegate);
        final Expression right = binExpr.right().accept(delegate);
        ret = (left == binExpr.left() && right == binExpr.right()) ? binExpr : left.compose(binExpr.op(), right);
        return cache(binExpr, ret);
    }

    /**
     * Calls lookup(unaryExpr) and returns the cached value, if any. If a
     * replacement has not been cached, visits the expression's child. If nothing
     * changes, the argument is cached and returned, otherwise a replacement
     * expression is cached and returned.
     *
     * @return { u: UnaryExpression | u.left = unaryExpr.expression.accept(delegate)
     *         && u.op = unaryExpr.op }
     */
    @Override
    public Expression visit(UnaryExpression unaryExpr) {
        Expression ret = lookup(unaryExpr);
        if (ret != null)
            return ret;

        final Expression child = unaryExpr.expression().accept(delegate);
        ret = (child == unaryExpr.expression()) ? unaryExpr : child.apply(unaryExpr.op());
        return cache(unaryExpr, ret);
    }

    /**
     * Calls lookup(comprehension) and returns the cached value, if any. If a
     * replacement has not been cached, visits the expression's children. If nothing
     * changes, the argument is cached and returned, otherwise a replacement
     * expression is cached and returned.
     *
     * @return { c: Comprehension | c.declarations =
     *         comprehension.declarations.accept(delegate) && c.formula =
     *         comprehension.formula.accept(delegate) }
     */
    @Override
    public Expression visit(Comprehension comprehension) {
        Expression ret = lookup(comprehension);
        if (ret != null)
            return ret;

        final Decls decls = comprehension.decls().accept(delegate);
        final Formula formula = comprehension.formula().accept(delegate);
        ret = (decls == comprehension.decls() && formula == comprehension.formula()) ? comprehension : formula.comprehension(decls);
        return cache(comprehension, ret);
    }

    /**
     * Calls lookup(ifExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's children. If nothing changes,
     * the argument is cached and returned, otherwise a replacement expression is
     * cached and returned.
     *
     * @return { i: IfExpression | i.condition = ifExpr.condition.accept(delegate)
     *         && i.thenExpr = ifExpr.thenExpr.accept(delegate) && i.elseExpr =
     *         ifExpr.elseExpr.accept(delegate) }
     */
    @Override
    public Expression visit(IfExpression ifExpr) {
        Expression ret = lookup(ifExpr);
        if (ret != null)
            return ret;

        final Formula condition = ifExpr.condition().accept(delegate);
        final Expression thenExpr = ifExpr.thenExpr().accept(delegate);
        final Expression elseExpr = ifExpr.elseExpr().accept(delegate);
        ret = (condition == ifExpr.condition() && thenExpr == ifExpr.thenExpr() && elseExpr == ifExpr.elseExpr()) ? ifExpr : condition.thenElse(thenExpr, elseExpr);
        return cache(ifExpr, ret);
    }

    /**
     * Calls lookup(decls) and returns the cached value, if any. If a replacement
     * has not been cached, visits each of the children's variable and expression.
     * If nothing changes, the argument is cached and returned, otherwise a
     * replacement Decls object is cached and returned.
     *
     * @return { d: Decls | d.size = decls.size && all i: [0..d.size) |
     *         d.declarations[i] = decls.declarations[i].accept(delegate) }
     */
    @Override
    public Expression visit(ProjectExpression project) {
        Expression ret = lookup(project);
        if (ret != null)
            return ret;

        final Expression expr = project.expression().accept(delegate);
        final IntExpression[] cols = new IntExpression[project.arity()];
        boolean allSame = expr == project.expression();
        for (int i = 0, arity = project.arity(); i < arity; i++) {
            cols[i] = project.column(i).accept(delegate);
            allSame = allSame && (cols[i] == project.column(i));
        }
        ret = allSame ? project : expr.project(cols);
        return cache(project, ret);
    }

    /**
     * Calls lookup(castExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's child. If nothing changes, the
     * argument is cached and returned, otherwise a replacement expression is cached
     * and returned.
     *
     * @return { e: Expression | e =
     *         castExpr.intExpr.accept(delegate).toExpression() }
     */
    @Override
    public Expression visit(IntToExprCast castExpr) {
        Expression ret = lookup(castExpr);
        if (ret != null)
            return ret;

        final IntExpression intExpr = castExpr.intExpr().accept(delegate);
        ret = (intExpr == castExpr.intExpr()) ? castExpr : intExpr.cast(castExpr.op());
        return cache(castExpr, ret);
    }

    /**
     * Calls lookup(intconst) and returns the cached value, if any. If a replacement
     * has not been cached, the constant is cached and returned.
     *
     * @return intconst
     */
    @Override
    public IntExpression visit(IntConstant intconst) {
        IntExpression ret = lookup(intconst);
        return ret == null ? cache(intconst, intconst) : intconst;
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's children. If nothing changes,
     * the argument is cached and returned, otherwise a replacement expression is
     * cached and returned.
     *
     * @return { i: IfIntExpression | i.condition =
     *         intExpr.condition.accept(delegate) && i.thenExpr =
     *         intExpr.thenExpr.accept(delegate) && i.elseExpr =
     *         intExpr.elseExpr.accept(delegate) }
     */
    @Override
    public IntExpression visit(IfIntExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final Formula condition = intExpr.condition().accept(delegate);
        final IntExpression thenExpr = intExpr.thenExpr().accept(delegate);
        final IntExpression elseExpr = intExpr.elseExpr().accept(delegate);
        ret = (condition == intExpr.condition() && thenExpr == intExpr.thenExpr() && elseExpr == intExpr.elseExpr()) ? intExpr : condition.thenElse(thenExpr, elseExpr);
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's child. If nothing changes, the
     * argument is cached and returned, otherwise a replacement expression is cached
     * and returned.
     *
     * @return { i: ExprToIntCast | i.expression =
     *         intExpr.expression.accept(delegate) && i.op = intExpr.op}
     */
    @Override
    public IntExpression visit(ExprToIntCast intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final Expression expr = intExpr.expression().accept(delegate);
        ret = expr == intExpr.expression() ? intExpr : expr.apply(intExpr.op());
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the intExpr's children. If nothing changes, the
     * argument is cached and returned, otherwise a replacement intExpr is cached
     * and returned.
     *
     * @return { e: IntExpression | e.op = intExpr.op && #e.children =
     *         #intExpr.children && all i: [0..intExpr.children) | e.child(i) =
     *         intExpr.child(i).accept(delegate) }
     */
    @Override
    public IntExpression visit(NaryIntExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final IntExpression[] visited = new IntExpression[intExpr.size()];
        boolean allSame = true;
        for (int i = 0; i < visited.length; i++) {
            final IntExpression child = intExpr.child(i);
            visited[i] = child.accept(delegate);
            allSame = allSame && visited[i] == child;
        }

        ret = allSame ? intExpr : IntExpression.compose(intExpr.op(), visited);
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's children. If nothing changes,
     * the argument is cached and returned, otherwise a replacement expression is
     * cached and returned.
     *
     * @return { c: IntExpression | [[c]] = intExpr.left.accept(delegate) op
     *         intExpr.right.accept(delegate) }
     */
    @Override
    public IntExpression visit(BinaryIntExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final IntExpression left = intExpr.left().accept(delegate);
        final IntExpression right = intExpr.right().accept(delegate);
        ret = (left == intExpr.left() && right == intExpr.right()) ? intExpr : left.compose(intExpr.op(), right);
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's child. If nothing changes, the
     * argument is cached and returned, otherwise a replacement expression is cached
     * and returned.
     *
     * @return { u: UnaryIntExpression | u.expression =
     *         intExpr.expression.accept(delegate) && u.op = intExpr.op }
     */
    @Override
    public IntExpression visit(UnaryIntExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final IntExpression child = intExpr.intExpr().accept(delegate);
        ret = (child == intExpr.intExpr()) ? intExpr : child.apply(intExpr.op());
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If a replacement
     * has not been cached, visits the expression's children. If nothing changes,
     * the argument is cached and returned, otherwise a replacement expression is
     * cached and returned.
     *
     * @return { c: IntExpression | [[c]] = sum intExpr.decls.accept(delegate) |
     *         intExpr.intExpr.accept(delegate) }
     */
    @Override
    public IntExpression visit(SumExpression intExpr) {
        IntExpression ret = lookup(intExpr);
        if (ret != null)
            return ret;

        final Decls decls = intExpr.decls().accept(delegate);
        final IntExpression expr = intExpr.intExpr().accept(delegate);
        ret = (decls == intExpr.decls() && expr == intExpr.intExpr()) ? intExpr : expr.sum(decls);
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intComp) and returns the cached value, if any. If a replacement
     * has not been cached, visits the formula's children. If nothing changes, the
     * argument is cached and returned, otherwise a replacement formula is cached
     * and returned.
     *
     * @return { c: Formula | [[c]] = intComp.left.accept(delegate) op
     *         intComp.right.accept(delegate) }
     */
    @Override
    public Formula visit(IntComparisonFormula intComp) {
        Formula ret = lookup(intComp);
        if (ret != null)
            return ret;

        final IntExpression left = intComp.left().accept(delegate);
        final IntExpression right = intComp.right().accept(delegate);
        ret = (left == intComp.left() && right == intComp.right()) ? intComp : left.compare(intComp.op(), right);
        return cache(intComp, ret);
    }

    /**
     * Calls lookup(constant) and returns the cached value, if any. If a replacement
     * has not been cached, the constant is cached and returned.
     *
     * @return constant
     */
    @Override
    public Formula visit(ConstantFormula constant) {
        final Formula ret = lookup(constant);
        return ret == null ? cache(constant, constant) : constant;
    }

    /**
     * Calls lookup(quantFormula) and returns the cached value, if any. If a
     * replacement has not been cached, visits the formula's children. If nothing
     * changes, the argument is cached and returned, otherwise a replacement formula
     * is cached and returned.
     *
     * @return { q: QuantifiedFormula | q.declarations =
     *         quantFormula.declarations.accept(delegate) && q.formula =
     *         quantFormula.formula.accept(delegate) }
     */
    @Override
    public Formula visit(QuantifiedFormula quantFormula) {
        Formula ret = lookup(quantFormula);
        if (ret != null)
            return ret;

        final Decls decls = quantFormula.decls().accept(delegate);
        final Formula domain = quantFormula.domain().accept(delegate);
        final Formula body = quantFormula.body().accept(delegate);
        ret = (decls == quantFormula.decls() && domain == quantFormula.domain() && body == quantFormula.body()) ? quantFormula : body.quantify(quantFormula.quantifier(), decls, domain);
        return cache(quantFormula, ret);
    }

    /**
     * Calls lookup(formula) and returns the cached value, if any. If a replacement
     * has not been cached, visits the formula's children. If nothing changes, the
     * argument is cached and returned, otherwise a replacement formula is cached
     * and returned.
     *
     * @return { e: Expression | e.op = formula.op && #e.children =
     *         #formula.children && all i: [0..formula.children) | e.child(i) =
     *         formula.child(i).accept(delegate) }
     */
    @Override
    public Formula visit(NaryFormula formula) {
        Formula ret = lookup(formula);
        if (ret != null)
            return ret;

        final Formula[] visited = new Formula[formula.size()];
        boolean allSame = true;
        for (int i = 0; i < visited.length; i++) {
            final Formula child = formula.child(i);
            visited[i] = child.accept(delegate);
            allSame = allSame && visited[i] == child;
        }

        ret = allSame ? formula : Formula.compose(formula.op(), visited);
        return cache(formula, ret);
    }

    /**
     * Calls lookup(binFormula) and returns the cached value, if any. If a
     * replacement has not been cached, visits the formula's children. If nothing
     * changes, the argument is cached and returned, otherwise a replacement formula
     * is cached and returned.
     *
     * @return { b: BinaryFormula | b.left = binExpr.left.accept(delegate) &&
     *         b.right = binExpr.right.accept(delegate) && b.op = binExpr.op }
     */
    @Override
    public Formula visit(BinaryFormula binFormula) {
        Formula ret = lookup(binFormula);
        if (ret != null)
            return ret;

        final Formula left = binFormula.left().accept(delegate);
        final Formula right = binFormula.right().accept(delegate);
        ret = (left == binFormula.left() && right == binFormula.right()) ? binFormula : left.compose(binFormula.op(), right);
        return cache(binFormula, ret);
    }

    /**
     * Calls lookup(binFormula) and returns the cached value, if any. If a
     * replacement has not been cached, visits the formula's child. If nothing
     * changes, the argument is cached and returned, otherwise a replacement formula
     * is cached and returned.
     *
     * @return { n: NotFormula | n.child = not.child.accept(delegate) }
     */
    @Override
    public Formula visit(NotFormula not) {
        Formula ret = lookup(not);
        if (ret != null)
            return ret;

        final Formula child = not.formula().accept(delegate);
        ret = (child == not.formula()) ? not : child.not();
        return cache(not, ret);
    }

    /**
     * Calls lookup(compFormula) and returns the cached value, if any. If a
     * replacement has not been cached, visits the formula's children. If nothing
     * changes, the argument is cached and returned, otherwise a replacement formula
     * is cached and returned.
     *
     * @return { c: ComparisonFormula | c.left = compFormula.left.accept(delegate)
     *         && c.right = compFormula.right.accept(delegate) && c.op =
     *         compFormula.op }
     */
    @Override
    public Formula visit(ComparisonFormula compFormula) {
        Formula ret = lookup(compFormula);
        if (ret != null)
            return ret;

        final Expression left = compFormula.left().accept(delegate);
        final Expression right = compFormula.right().accept(delegate);
        ret = (left == compFormula.left() && right == compFormula.right()) ? compFormula : left.compare(compFormula.op(), right);
        return cache(compFormula, ret);
    }

    /**
     * Calls lookup(multFormula) and returns the cached value, if any. If a
     * replacement has not been cached, visits the formula's children. If nothing
     * changes, the argument is cached and returned, otherwise a replacement formula
     * is cached and returned.
     *
     * @return { m: MultiplicityFormula | m.multiplicity = multFormula.multiplicity
     *         && m.expression = multFormula.expression.accept(delegate) }
     */
    @Override
    public Formula visit(MultiplicityFormula multFormula) {
        Formula ret = lookup(multFormula);
        if (ret != null)
            return ret;

        final Expression expression = multFormula.expression().accept(delegate);
        ret = (expression == multFormula.expression()) ? multFormula : expression.apply(multFormula.multiplicity());
        return cache(multFormula, ret);
    }

    /**
     * Calls lookup(pred) and returns the cached value, if any. If a replacement has
     * not been cached, visits the formula's children. If nothing changes, the
     * argument is cached and returned, otherwise a replacement formula is cached
     * and returned.
     *
     * @return { p: RelationPredicate | p.name = pred.name && p.relation =
     *         pred.relation.accept(delegate) && p.name = FUNCTION => p.targetMult =
     *         pred.targetMult && p.domain = pred.domain.accept(delegate) && p.range
     *         = pred.range.accept(delegate), p.name = TOTAL_ORDERING => p.ordered =
     *         pred.ordered.accept(delegate) && p.first =
     *         pred.first.accept(delegate) && p.last = pred.last.accept(delegate) }
     */
    @Override
    public Formula visit(RelationPredicate pred) {
        Formula ret = lookup(pred);
        if (ret != null)
            return ret;

        final Relation r = (Relation) pred.relation().accept(delegate);
        switch (pred.name()) {
            case ACYCLIC :
                ret = (r == pred.relation()) ? pred : r.acyclic();
                break;
            case FUNCTION :
                final RelationPredicate.Function fp = (RelationPredicate.Function) pred;
                final Expression domain = fp.domain().accept(delegate);
                final Expression range = fp.range().accept(delegate);
                ret = (r == fp.relation() && domain == fp.domain() && range == fp.range()) ? fp : (fp.targetMult() == Multiplicity.ONE ? r.function(domain, range) : r.partialFunction(domain, range));
                break;
            case TOTAL_ORDERING :
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) pred;
                final Relation ordered = (Relation) tp.ordered().accept(delegate);
                final Relation first = (Relation) tp.first().accept(delegate);
                final Relation last = (Relation) tp.last().accept(delegate);
                ret = (r == tp.relation() && ordered == tp.ordered() && first == tp.first() && last == tp.last()) ? tp : r.totalOrder(ordered, first, last);
                break;
            default :
                throw new IllegalArgumentException("unknown relation predicate: " + pred.name());
        }
        return cache(pred, ret);
    }

    @Override
    public Formula visit(FixFormula fixFormula) {
        Formula ret = lookup(fixFormula);
        if (ret != null)
            return ret;
        final Formula formula = fixFormula.formula().accept(delegate);
        final Formula condition = fixFormula.condition().accept(delegate);
        ret = (formula == fixFormula.formula() && condition == fixFormula.condition()) ? fixFormula : formula.fix(condition);
        return cache(fixFormula, ret);
    }

}
