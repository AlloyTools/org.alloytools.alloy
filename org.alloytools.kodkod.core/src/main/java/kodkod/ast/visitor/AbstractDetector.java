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

/**
 * <p>
 * A depth first detector. Subclasses should override the methods in which
 * detection is performed to return TRUE. For example, a Variable detector could
 * be implemented simply by subclassing this implementation and overriding the
 * {@link #visit(Variable) } method to return TRUE.
 * </p>
 *
 * @specfield cached: set Node // result of visiting these nodes will be cached
 * @specfield cache: Node -> lone Boolean
 * @specfield cached in cache.Node
 * @author Emina Torlak
 */
public abstract class AbstractDetector implements ReturnVisitor<Boolean,Boolean,Boolean,Boolean> {

    protected final Map<Node,Boolean> cache;
    protected final Set<Node>         cached;

    /**
     * Constructs a depth first detector which will cache the results of visiting
     * the given nodes and re-use them on subsequent visits.
     *
     * @ensures this.cached' = cached && no this.cache
     */
    protected AbstractDetector(Set<Node> cached) {
        this.cached = cached;
        this.cache = new IdentityHashMap<Node,Boolean>(cached.size());
    }

    /**
     * Constructs a depth-first detector which will cache the results of visiting
     * the given nodes in the given map, and re-use them on subsequent visits.
     *
     * @ensures this.cached' = cached && this.cache' = cache
     */
    protected AbstractDetector(Set<Node> cached, Map<Node,Boolean> cache) {
        this.cached = cached;
        this.cache = cache;
    }

    /**
     * If n has been visited and a value for it cached, the cached value is
     * returned. Otherwise null is returned.
     *
     * @return this.cache[n]
     */
    protected Boolean lookup(Node n) {
        return cache.get(n);
    }

    /**
     * Caches the given value for the specified node, if this is a caching visitor,
     * and returns Boolean.valueOf(val).
     *
     * @ensures n in this.cached => this.cache' = this.cache ++
     *          n->Boolean.valueOf(val), this.cache' = this.cache
     * @return Boolean.valueOf(val)
     */
    protected Boolean cache(Node n, boolean val) {
        final Boolean ret = Boolean.valueOf(val);
        if (cached.contains(n))
            cache.put(n, ret);
        return ret;
    }

    /**
     * Calls lookup(decls) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the disjunction of the children's return
     * values and returns it.
     *
     * @return let x = lookup(decls) | x != null => x, cache(decls, some d:
     *         decls.declarations | d.accept(this))
     */
    @Override
    public Boolean visit(Decls decls) {
        final Boolean ret = lookup(decls);
        if (ret != null)
            return ret;
        for (Decl d : decls) {
            if (visit(d))
                return cache(decls, true);
        }
        return cache(decls, false);
    }

    /**
     * Calls lookup(decl) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the disjunction of the children's return
     * values and returns it.
     *
     * @return let x = lookup(decl) | x != null => x, cache(decl,
     *         decl.variable.accept(this) || decl.expression.accept(this))
     */
    @Override
    public Boolean visit(Decl decl) {
        final Boolean ret = lookup(decl);
        return (ret != null) ? ret : cache(decl, decl.variable().accept(this) || decl.expression().accept(this));
    }

    /**
     * Returns FALSE.
     *
     * @return FALSE
     */
    @Override
    public Boolean visit(Relation relation) {
        return Boolean.FALSE;
    }

    /**
     * Returns FALSE.
     *
     * @return FALSE
     */
    @Override
    public Boolean visit(Variable variable) {
        return Boolean.FALSE;
    }

    /**
     * Returns FALSE.
     *
     * @return FALSE
     */
    @Override
    public Boolean visit(ConstantExpression expr) {
        return Boolean.FALSE;
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the disjunction of the children's return
     * values and returns it.
     *
     * @return let x = lookup(expr) | x != null => x, cache(expr,
     *         expr.child(0).accept(this) || ... ||
     *         expr.child(expr.size()-1).accept(this))
     */
    @Override
    public Boolean visit(NaryExpression expr) {
        final Boolean ret = lookup(expr);
        if (ret != null)
            return ret;
        for (Expression child : expr) {
            if (child.accept(this))
                return cache(expr, true);
        }
        return cache(expr, false);
    }

    /**
     * Calls lookup(binExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(binExpr) | x != null => x, cache(binExpr,
     *         binExpr.left.accept(this) || binExpr.right.accept(this))
     */
    @Override
    public Boolean visit(BinaryExpression binExpr) {
        final Boolean ret = lookup(binExpr);
        return (ret != null) ? ret : cache(binExpr, binExpr.left().accept(this) || binExpr.right().accept(this));
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If no cached value
     * exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(expr) | x != null => x, cache(expr,
     *         expr.expression.accept(this))
     */
    @Override
    public Boolean visit(UnaryExpression expr) {
        final Boolean ret = lookup(expr);
        return (ret != null) ? ret : cache(expr, expr.expression().accept(this));
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the disjunction of the children's return
     * values and returns it.
     *
     * @return let x = lookup(expr) | x != null => x, cache(expr,
     *         expr.decls.accept(this) || expr.formula.accept(this))
     */
    @Override
    public Boolean visit(Comprehension expr) {
        final Boolean ret = lookup(expr);
        return (ret != null) ? ret : cache(expr, expr.decls().accept(this) || expr.formula().accept(this));
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the disjunction of the children's return
     * values and returns it.
     *
     * @return let x = lookup(expr) | x != null => x, cache(expr,
     *         expr.condition.accept(this) || expr.thenExpr.accept(this) ||
     *         expr.elseExpr.accept(this))
     */
    @Override
    public Boolean visit(IfExpression expr) {
        final Boolean ret = lookup(expr);
        return (ret != null) ? ret : cache(expr, expr.condition().accept(this) || expr.thenExpr().accept(this) || expr.elseExpr().accept(this));
    }

    /**
     * Calls lookup(project) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(project) | x != null => x, cache(project,
     *         project.expression.accept(this) || project.columns[int].accept(this))
     */
    @Override
    public Boolean visit(ProjectExpression project) {
        final Boolean ret = lookup(project);
        if (ret != null)
            return ret;
        if (project.expression().accept(this))
            return cache(project, true);
        for (int i = 0, arity = project.arity(); i < arity; i++) {
            if (project.column(i).accept(this))
                return cache(project, true);
        }
        return cache(project, false);
    }

    /**
     * Calls lookup(castExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(castExpr) | x != null => x, cache(intExpr,
     *         castExpr.intExpr.accept(this))
     */
    @Override
    public Boolean visit(IntToExprCast castExpr) {
        final Boolean ret = lookup(castExpr);
        return (ret != null) ? ret : cache(castExpr, castExpr.intExpr().accept(this));
    }

    /**
     * Returns FALSE.
     *
     * @return FALSE
     */
    @Override
    public Boolean visit(IntConstant intConst) {
        return Boolean.FALSE;
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.condition.accept(this) || intExpr.thenExpr.accept(this) ||
     *         intExpr.elseExpr.accept(this))
     */
    @Override
    public Boolean visit(IfIntExpression intExpr) {
        final Boolean ret = lookup(intExpr);
        return (ret != null) ? ret : cache(intExpr, intExpr.condition().accept(this) || intExpr.thenExpr().accept(this) || intExpr.elseExpr().accept(this));
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.expression.accept(this))
     */
    @Override
    public Boolean visit(ExprToIntCast intExpr) {
        final Boolean ret = lookup(intExpr);
        return (ret != null) ? ret : cache(intExpr, intExpr.expression().accept(this));
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.child(0).accept(this) || ... ||
     *         intExpr.child(intExpr.size()-1).accept(this))
     */
    @Override
    public Boolean visit(NaryIntExpression intExpr) {
        final Boolean ret = lookup(intExpr);
        if (ret != null)
            return ret;
        for (IntExpression child : intExpr) {
            if (child.accept(this))
                return cache(intExpr, true);
        }
        return cache(intExpr, false);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.left.accept(this) || intExpr.right.accept(this))
     */
    @Override
    public Boolean visit(BinaryIntExpression intExpr) {
        final Boolean ret = lookup(intExpr);
        return (ret != null) ? ret : cache(intExpr, intExpr.left().accept(this) || intExpr.right().accept(this));
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.expression.accept(this))
     */
    @Override
    public Boolean visit(UnaryIntExpression intExpr) {
        final Boolean ret = lookup(intExpr);
        return (ret != null) ? ret : cache(intExpr, intExpr.intExpr().accept(this));
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.decls.accept(this) || intExpr.intExpr.accept(this))
     */
    @Override
    public Boolean visit(SumExpression intExpr) {
        final Boolean ret = lookup(intExpr);
        return (ret != null) ? ret : cache(intExpr, intExpr.decls().accept(this) || intExpr.intExpr().accept(this));
    }

    /**
     * Calls lookup(intComp) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(intComp) | x != null => x, cache(intComp,
     *         intComp.left.accept(this) || intComp.right.accept(this))
     */
    @Override
    public Boolean visit(IntComparisonFormula intComp) {
        final Boolean ret = lookup(intComp);
        return (ret != null) ? ret : cache(intComp, intComp.left().accept(this) || intComp.right().accept(this));
    }

    /**
     * Calls lookup(quantFormula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(quantFormula) | x != null => x, cache(quantFormula,
     *         quantFormula.declarations.accept(this)
     *         ||quantFormula.formula.accept(this))
     */
    @Override
    public Boolean visit(QuantifiedFormula quantFormula) {
        final Boolean ret = lookup(quantFormula);
        return (ret != null) ? ret : cache(quantFormula, quantFormula.decls().accept(this) || quantFormula.formula().accept(this));
    }

    /**
     * Calls lookup(formula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(formula) | x != null => x, cache(formula,
     *         formula.child(0).accept(this) || ... ||
     *         formula.child(formula.size()-1).accept(this))
     */
    @Override
    public Boolean visit(NaryFormula formula) {
        final Boolean ret = lookup(formula);
        if (ret != null)
            return ret;
        for (Formula child : formula) {
            if (child.accept(this))
                return cache(formula, true);
        }
        return cache(formula, false);
    }

    /**
     * Calls lookup(binFormula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(binFormula) | x != null => x, cache(binFormula,
     *         binFormula.left.accept(this) || binFormula.right.accept(this))
     */
    @Override
    public Boolean visit(BinaryFormula binFormula) {
        final Boolean ret = lookup(binFormula);
        return (ret != null) ? ret : cache(binFormula, binFormula.left().accept(this) || binFormula.right().accept(this));
    }

    /**
     * Calls lookup(not) and returns the cached value, if any. If no cached value
     * exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(not) | x != null => x, cache(not,
     *         not.formula.accept(this))
     */
    @Override
    public Boolean visit(NotFormula not) {
        final Boolean ret = lookup(not);
        return (ret != null) ? ret : cache(not, not.formula().accept(this));
    }

    /**
     * Returns FALSE.
     *
     * @return FALSE
     */
    @Override
    public Boolean visit(ConstantFormula constant) {
        return Boolean.FALSE;
    }

    /**
     * Calls lookup(exprComp) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(exprComp) | x != null => x,
     *         cache(exprComp,exprComp.left.accept(this) ||
     *         exprComp.right.accept(this))
     */
    @Override
    public Boolean visit(ComparisonFormula exprComp) {
        final Boolean ret = lookup(exprComp);
        return (ret != null) ? ret : cache(exprComp, exprComp.left().accept(this) || exprComp.right().accept(this));
    }

    /**
     * Calls lookup(multFormula) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(multFormula) | x != null => x, cache(multFormula,
     *         multFormula.expression.accept(this))
     */
    @Override
    public Boolean visit(MultiplicityFormula multFormula) {
        final Boolean ret = lookup(multFormula);
        return (ret != null) ? ret : cache(multFormula, multFormula.expression().accept(this));
    }

    /**
     * Calls lookup(predicate) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the disjunction of the children's
     * return values and returns it.
     *
     * @return let x = lookup(predicate) | x != null => x, cache(predicate, some n:
     *         predicate.children | n.accept(this))
     */
    @Override
    public Boolean visit(RelationPredicate predicate) {
        final Boolean ret = lookup(predicate);
        if (ret != null)
            return ret;
        if (predicate.relation().accept(this))
            return cache(predicate, true);
        if (predicate.name() == RelationPredicate.Name.FUNCTION) {
            final RelationPredicate.Function fp = (RelationPredicate.Function) predicate;
            return cache(predicate, fp.domain().accept(this) || fp.range().accept(this));
        } else if (predicate.name() == RelationPredicate.Name.TOTAL_ORDERING) {
            final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) predicate;
            return cache(predicate, tp.ordered().accept(this) || tp.first().accept(this) || tp.last().accept(this));
        }
        return cache(predicate, false);
    }

    @Override
    public Boolean visit(FixFormula fixFormula) {
        final Boolean ret = lookup(fixFormula);
        return (ret != null) ? ret : cache(fixFormula, fixFormula.formula().accept(this) || fixFormula.condition().accept(this));
    }

}
