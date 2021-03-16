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

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import kodkod.ast.Comprehension;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.SumExpression;
import kodkod.ast.Variable;
import kodkod.ast.visitor.AbstractCollector;
import kodkod.util.collections.ArrayStack;
import kodkod.util.collections.Stack;

/**
 * Collects free variables in a given Node. Subclasses can customize the
 * collection policy by overriding the <tt>cache</tt> method. By default, the
 * cache will contain only the free variables of the shared nodes. The default
 * implementation of {@link #newSet()} ensures that the collected free variables
 * will be returned in the order in which they were encountered during
 * traversal.
 *
 * @specfield cached: set Node
 * @specfield cache: Node -> lone Set<Variable>
 * @specfield varsInScope: Stack<Variable> // variables currently in scope
 * @author Emina Torlak
 */
abstract class FreeVariableCollector extends AbstractCollector<Variable> {

    /*
     * Holds the variables that are currently in scope, with the variable at the top
     * of the stack being the last declared variable.
     */
    protected final Stack<Variable> varsInScope;

    /**
     * Constructs a new collector using the given structural information. The given
     * set is required to contain the syntactically shared subtrees of the node for
     * which we are computing caching information.
     */
    protected FreeVariableCollector(Set<Node> cached) {
        super(cached);
        this.varsInScope = new ArrayStack<Variable>();
    }

    /**
     * @see kodkod.ast.visitor.AbstractCollector#newSet()
     */
    @Override
    protected Set<Variable> newSet() {
        return new LinkedHashSet<Variable>(2);
    }

    /**
     * Visits the given comprehension, quantified formula, or sum expression. The
     * method returns a set that contains all the free variables in the declarations
     * and the body, minus the variables that are actually bound in the
     * declarations.
     */
    @SuppressWarnings("unchecked" )
    private Set<Variable> visit(Node creator, Decls decls, Node body) {
        Set<Variable> ret = lookup(creator);
        if (ret != null)
            return ret;

        ret = newSet();
        final Set<Variable> boundVars = newSet();

        // add the declared variables to the scoped variables stack;
        // compute free vars for each decl, and the difference of the
        // computed set and previously bound variables to ret
        for (Decl decl : decls) {
            for (Variable v : visit(decl)) {
                if (!boundVars.contains(v))
                    ret.add(v);
            }
            varsInScope.push(decl.variable());
            boundVars.add(decl.variable());
        }

        // add to ret the free variables in the body, minus the bound variables
        for (Variable v : (Set<Variable>) body.accept(this)) {
            if (!boundVars.contains(v))
                ret.add(v);
        }

        // remove the declared variables from the in-scope stack
        for (int i = decls.size(); i > 0; i--) {
            varsInScope.pop();
        }

        return cache(creator, ret);
    }

    /**
     * Returns the free variables in the given declaration.
     *
     * @return freeVars(decl.expression)
     */
    @Override
    public Set<Variable> visit(Decl decl) {
        final Set<Variable> ret = lookup(decl);
        return ret != null ? ret : cache(decl, decl.expression().accept(this));
    }

    /**
     * Returns the singleton set containing the given variable.
     *
     * @return {variable}
     */
    @Override
    public Set<Variable> visit(Variable variable) {
        return cache(variable, Collections.singleton(variable));
    }

    /**
     * Calls lookup(comprehension) and returns the cached value, if any. If no
     * cached value exists, computes, caches and returns the set of free variables
     * in comprehension.
     *
     * @return let x = lookup(comprehension), d = comprehension.declarations, f =
     *         comprehension.formula | x != null => x, cache(comprehension,
     *         (f.accept(this) - d.children.variable) + {v: Variable | some i:
     *         [0..d.size) | v in d.declarations[i].accept(this) -
     *         d.declarations[0..i).variable } )
     */
    @Override
    public Set<Variable> visit(Comprehension comprehension) {
        return visit(comprehension, comprehension.decls(), comprehension.formula());
    }

    /**
     * Calls lookup(intExpr) and returns the cached value, if any. If no cached
     * value exists, computes, caches and returns the set of free variables in
     * intExpr.
     *
     * @return let x = lookup(intExpr), d = intExpr.declarations, e =
     *         intExpr.intExpr | x != null => x, cache(intExpr, (e.accept(this) -
     *         d.children.variable) + {v: Variable | some i: [0..d.size) | v in
     *         d.declarations[i].accept(this) - d.declarations[0..i).variable } )
     */
    @Override
    public Set<Variable> visit(SumExpression intExpr) {
        return visit(intExpr, intExpr.decls(), intExpr.intExpr());
    }

    /**
     * Calls lookup(quantFormula) and returns the cached value, if any. If no cached
     * value exists, computes, caches and returns the set of free variables in
     * quantFormula.
     *
     * @return let x = lookup(quantFormula), d = quantFormula.declarations, f =
     *         quantFormula.formula | x != null => x, cache(quantFormula,
     *         (f.accept(this) - d.children.variable) + {v: Variable | some i:
     *         [0..d.size) | v in d.declarations[i].accept(this) -
     *         d.declarations[0..i).variable } )
     */
    @Override
    public Set<Variable> visit(QuantifiedFormula quantFormula) {
        return visit(quantFormula, quantFormula.decls(), quantFormula.formula());
    }
}
