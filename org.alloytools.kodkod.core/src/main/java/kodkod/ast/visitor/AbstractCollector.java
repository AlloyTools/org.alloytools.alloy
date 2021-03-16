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

import java.util.Collections;
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
 * A depth first collector. Subclasses should override the methods in which
 * detection is performed to return the appropriate set. For example, a Variable
 * collector could be implemented simply by subclassing this implementation and
 * overriding the {@link #visit(Variable) } method to return a singleton set
 * containing the input argument.
 * </p>
 *
 * @specfield cached: set Node // result of visiting these nodes will be cached
 * @specfield cache: Node -> lone Set<T>
 * @specfield cached in cache.Node
 * @author Emina Torlak
 */
public abstract class AbstractCollector<T> implements ReturnVisitor<Set<T>,Set<T>,Set<T>,Set<T>> {

    protected final Map<Node,Set<T>> cache;
    protected final Set<Node>        cached;

    /**
     * Constructs a depth first collector which will cache the results of visiting
     * the given nodes and re-use them on subsequent visits.
     *
     * @ensures this.cached' = cached && no this.cache
     */
    protected AbstractCollector(Set<Node> cached) {
        this.cached = cached;
        this.cache = new IdentityHashMap<Node,Set<T>>(cached.size());
    }

    /**
     * Constructs a depth-first collectior which will cache the results of visiting
     * the given nodes in the given map, and re-use them on subsequent visits.
     *
     * @ensures this.cached' = cached && this.cache' = cache
     */
    protected AbstractCollector(Set<Node> cached, Map<Node,Set<T>> cache) {
        this.cached = cached;
        this.cache = cache;
    }

    /**
     * If n has been visited and a value for it cached, the cached value is
     * returned. Otherwise null is returned.
     *
     * @return this.cache[n]
     */
    protected Set<T> lookup(Node n) {
        return cache.get(n);
    }

    /**
     * Caches the given value for the specified node, if this is a caching visitor,
     * and returns it.
     *
     * @ensures n in this.cached => this.cache' = this.cache ++ n->reduce(val),
     *          this.cache' = this.cache
     * @return val
     */
    protected Set<T> cache(Node n, Set<T> val) {
        if (cached.contains(n)) {
            cache.put(n, reduce(val));
        }
        return val;
    }

    /**
     * Returns the set that has the same contents as val, but that may be more
     * efficiently implemented than val.
     *
     * @return val.size()=0 => Collections.EMPTY_SET, val.size()=1 =>
     *         Collections.singleton(val.iterator().next()), val
     */
    protected Set<T> reduce(Set<T> val) {
        switch (val.size()) {
            case 0 :
                return Collections.emptySet();
            case 1 :
                return Collections.singleton(val.iterator().next());
            default :
                return val;
        }
    }

    /**
     * Returns a new, empty, modifiable set.
     *
     * @return a new, empty, modifiable set.
     */
    protected abstract Set<T> newSet();

    /**
     * Calls lookup(decls) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the union of the sets returned by the
     * children and returns it.
     *
     * @return let x = lookup(decls) | x != null => x, cache(decls,
     *         decls.declarations[0].accept(this) +...+
     *         decls.declarations[decls.size-1].accept(this))
     */
    @Override
    public Set<T> visit(Decls decls) {
        Set<T> ret = lookup(decls);
        if (ret != null)
            return ret;
        ret = newSet();
        for (Decl d : decls) {
            ret.addAll(d.accept(this));
        }
        return cache(decls, ret);
    }

    /**
     * Calls lookup(decl) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the union of the sets returned by the
     * children and returns it.
     *
     * @return let x = lookup(decl) | x != null => x, cache(decls,
     *         decl.variable.accept(this) + decl.expression.accept(this))
     */
    @Override
    public Set<T> visit(Decl decl) {
        Set<T> ret = lookup(decl);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(decl.variable().accept(this));
        ret.addAll(decl.expression().accept(this));
        return cache(decl, ret);
    }

    /**
     * Returns Collections.EMPTY_SET
     *
     * @return Collections.EMPTY_SET
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Set<T> visit(Relation relation) {
        return Collections.EMPTY_SET;
    }

    /**
     * Returns Collections.EMPTY_SET
     *
     * @return Collections.EMPTY_SET
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Set<T> visit(Variable variable) {
        return Collections.EMPTY_SET;
    }

    /**
     * Returns Collections.EMPTY_SET
     *
     * @return Collections.EMPTY_SET
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Set<T> visit(ConstantExpression constExpr) {
        return Collections.EMPTY_SET;
    }

    /**
     * Calls lookup(expr) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the union of the children's return values
     * and returns it.
     *
     * @return let x = lookup(expr) | x != null => x, cache(expr,
     *         expr.child(0).accept(this) + .. +
     *         expr.child(expr.size()-1).accept(this))
     */
    @Override
    public Set<T> visit(NaryExpression expr) {
        Set<T> ret = lookup(expr);
        if (ret != null)
            return ret;
        ret = newSet();
        for (Expression child : expr) {
            ret.addAll(child.accept(this));
        }
        return cache(expr, ret);
    }

    /**
     * Calls lookup(binExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(binExpr) | x != null => x, cache(binExpr,
     *         binExpr.left.accept(this) + binExpr.right.accept(this))
     */
    @Override
    public Set<T> visit(BinaryExpression binExpr) {
        Set<T> ret = lookup(binExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(binExpr.left().accept(this));
        ret.addAll(binExpr.right().accept(this));
        return cache(binExpr, ret);
    }

    /**
     * Calls lookup(unaryExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(unaryExpr) | x != null => x, cache(unaryExpr,
     *         unaryExpr.expression.accept(this))
     */
    @Override
    public Set<T> visit(UnaryExpression unaryExpr) {
        Set<T> ret = lookup(unaryExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(unaryExpr.expression().accept(this));
        return cache(unaryExpr, ret);
    }

    /**
     * Calls lookup(comprehension) and returns the cached value, if any. If no
     * cached value exists, visits each child, caches the union of the children's
     * return values and returns it.
     *
     * @return let x = lookup(comprehension) | x != null => x, cache(comprehension,
     *         comprehension.declarations.accept(this) +
     *         comprehension.formula.accept(this))
     */
    @Override
    public Set<T> visit(Comprehension comprehension) {
        Set<T> ret = lookup(comprehension);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(comprehension.decls().accept(this));
        ret.addAll(comprehension.formula().accept(this));
        return cache(comprehension, ret);
    }

    /**
     * Calls lookup(ifExpr) and returns the cached value, if any. If no cached value
     * exists, visits each child, caches the union of the children's return values
     * and returns it.
     *
     * @return let x = lookup(ifExpr) | x != null => x, cache(ifExpr,
     *         ifExpr.condition.accept(this) + ifExpr.thenExpr.accept(this) +
     *         ifExpr.elseExpr.accept(this))
     */
    @Override
    public Set<T> visit(IfExpression ifExpr) {
        Set<T> ret = lookup(ifExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(ifExpr.condition().accept(this));
        ret.addAll(ifExpr.thenExpr().accept(this));
        ret.addAll(ifExpr.elseExpr().accept(this));
        return cache(ifExpr, ret);
    }

    /**
     * Calls lookup(project) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(project) | x != null => x, cache(project,
     *         project.expression.accept(this) + project.columns[int].accept(this))
     */
    @Override
    public Set<T> visit(ProjectExpression project) {
        Set<T> ret = lookup(project);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(project.expression().accept(this));
        for (int i = 0, arity = project.arity(); i < arity; i++) {
            ret.addAll(project.column(i).accept(this));
        }
        return cache(project, ret);
    }

    /**
     * Calls lookup(castExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(castExpr) | x != null => x, cache(intExpr,
     *         castExpr.intExpr.accept(this))
     */
    @Override
    public Set<T> visit(IntToExprCast castExpr) {
        Set<T> ret = lookup(castExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(castExpr.intExpr().accept(this));
        return cache(castExpr, ret);
    }

    /**
     * Returns Collections.EMPTY_SET
     *
     * @return Collections.EMPTY_SET
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Set<T> visit(IntConstant intConst) {
        return Collections.EMPTY_SET;
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.condition.accept(this) + intExpr.thenExpr.accept(this) +
     *         intExpr.elseExpr.accept(this))
     */
    @Override
    public Set<T> visit(IfIntExpression intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intExpr.condition().accept(this));
        ret.addAll(intExpr.thenExpr().accept(this));
        ret.addAll(intExpr.elseExpr().accept(this));
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.expression.accept(this))
     */
    @Override
    public Set<T> visit(ExprToIntCast intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intExpr.expression().accept(this));
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.child(0).accept(this) + .. +
     *         intExpr.child(intExpr.size()-1).accept(this))
     */
    @Override
    public Set<T> visit(NaryIntExpression intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        for (IntExpression child : intExpr) {
            ret.addAll(child.accept(this));
        }
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.left.accept(this) + intExpr.right.accept(this))
     */
    @Override
    public Set<T> visit(BinaryIntExpression intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intExpr.left().accept(this));
        ret.addAll(intExpr.right().accept(this));
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.expression.accept(this))
     */
    @Override
    public Set<T> visit(UnaryIntExpression intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intExpr.intExpr().accept(this));
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(intExpr) | x != null => x, cache(intExpr,
     *         intExpr.decls.accept(this) + intExpr.intExpr.accept(this))
     */
    @Override
    public Set<T> visit(SumExpression intExpr) {
        Set<T> ret = lookup(intExpr);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intExpr.decls().accept(this));
        ret.addAll(intExpr.intExpr().accept(this));
        return cache(intExpr, ret);
    }

    /**
     * Calls lookup(intComp) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(intComp) | x != null => x, cache(intComp,
     *         intComp.left.accept(this) + intComp.right.accept(this))
     */
    @Override
    public Set<T> visit(IntComparisonFormula intComp) {
        Set<T> ret = lookup(intComp);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(intComp.left().accept(this));
        ret.addAll(intComp.right().accept(this));
        return cache(intComp, ret);
    }

    /**
     * Calls lookup(quantFormula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(quantFormula) | x != null => x, cache(quantFormula,
     *         quantFormula.declarations.accept(this) +
     *         quantFormula.formula.accept(this))
     */
    @Override
    public Set<T> visit(QuantifiedFormula quantFormula) {
        Set<T> ret = lookup(quantFormula);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(quantFormula.decls().accept(this));
        ret.addAll(quantFormula.formula().accept(this));
        return cache(quantFormula, ret);
    }

    /**
     * Calls lookup(formula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(formula) | x != null => x, cache(formula,
     *         formula.child(0).accept(this) + .. +
     *         formula.child(formula.size()-1).accept(this))
     */
    @Override
    public Set<T> visit(NaryFormula formula) {
        Set<T> ret = lookup(formula);
        if (ret != null)
            return ret;
        ret = newSet();
        for (Formula child : formula) {
            ret.addAll(child.accept(this));
        }
        return cache(formula, ret);
    }

    /**
     * Calls lookup(binFormula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(binFormula) | x != null => x, cache(binFormula,
     *         binFormula.left.accept(this) + binFormula.right.accept(this))
     */
    @Override
    public Set<T> visit(BinaryFormula binFormula) {
        Set<T> ret = lookup(binFormula);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(binFormula.left().accept(this));
        ret.addAll(binFormula.right().accept(this));
        return cache(binFormula, ret);
    }

    /**
     * Calls lookup(not) and returns the cached value, if any. If no cached value
     * exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(not) | x != null => x, cache(not,
     *         not.formula.accept(this))
     */
    @Override
    public Set<T> visit(NotFormula not) {
        Set<T> ret = lookup(not);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(not.formula().accept(this));
        return cache(not, ret);
    }

    /**
     * Returns Collections.EMPTY_SET
     *
     * @return Collections.EMPTY_SET
     */
    @Override
    @SuppressWarnings("unchecked" )
    public Set<T> visit(ConstantFormula constant) {
        return Collections.EMPTY_SET;
    }

    /**
     * Calls lookup(compFormula) and returns the cached value, if any. If no cached
     * value exists, visits each child, caches the union of the children's return
     * values and returns it.
     *
     * @return let x = lookup(compFormula) | x != null => x,
     *         cache(compFormula,compFormula.left.accept(this) +
     *         compFormula.right.accept(this))
     */
    @Override
    public Set<T> visit(ComparisonFormula compFormula) {
        Set<T> ret = lookup(compFormula);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(compFormula.left().accept(this));
        ret.addAll(compFormula.right().accept(this));
        return cache(compFormula, ret);
    }

    /**
     * Calls lookup(multFormula) and returns the cached value, if any. If no cached
     * value exists, visits the child, caches its return value and returns it.
     *
     * @return let x = lookup(multFormula) | x != null => x, cache(multFormula,
     *         multFormula.expression.accept(this))
     */
    @Override
    public Set<T> visit(MultiplicityFormula multFormula) {
        Set<T> ret = lookup(multFormula);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(multFormula.expression().accept(this));
        return cache(multFormula, ret);
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
    public Set<T> visit(RelationPredicate pred) {
        Set<T> ret = lookup(pred);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(pred.relation().accept(this));
        switch (pred.name()) {
            case ACYCLIC :
                break;
            case FUNCTION :
                final RelationPredicate.Function fp = (RelationPredicate.Function) pred;
                ret.addAll(fp.domain().accept(this));
                ret.addAll(fp.range().accept(this));
                break;
            case TOTAL_ORDERING :
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) pred;
                ret.addAll(tp.ordered().accept(this));
                ret.addAll(tp.first().accept(this));
                ret.addAll(tp.last().accept(this));
                break;
            default :
                throw new IllegalArgumentException("unknown relation predicate: " + pred.name());
        }
        return cache(pred, ret);
    }

    @Override
    public Set<T> visit(FixFormula fixFormula) {
        Set<T> ret = lookup(fixFormula);
        if (ret != null)
            return ret;
        ret = newSet();
        ret.addAll(fixFormula.formula().accept(this));
        ret.addAll(fixFormula.condition().accept(this));
        return cache(fixFormula, ret);
    }

}
