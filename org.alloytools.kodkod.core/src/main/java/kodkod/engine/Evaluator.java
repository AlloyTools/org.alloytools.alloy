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
package kodkod.engine;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.engine.bool.BooleanConstant;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.Int;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translator;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

/**
 * An evaluator for relational formulas and expressions with respect to a given
 * {@link kodkod.instance.Instance instance} and
 * {@link kodkod.engine.config.Options options}.
 * <p>
 * <b>Note: </b> you may observe surprising (though correct) evaluator behavior
 * if you do not use the same set of integer options (i.e.
 * {@link kodkod.engine.config.Options#intEncoding() intEncoding} and
 * {@link kodkod.engine.config.Options#bitwidth() bitwidth} when evaluating and
 * solving a formula. For example, suppose that that an Instance i is a solution
 * to a formula f found using options o. If you create an evaluator e such that
 * e.instance = i, but e.options is an Options object with different integer
 * settings than o, e.evalate(f) may return false.
 * </p>
 *
 * @specfield options: Options
 * @specfield instance: Instance
 * @author Emina Torlak
 */
public final class Evaluator {

    private final Instance instance;
    private final Options  options;
    private boolean        wasOverflow;	// [AM] was overflow detected during
    // evaluation

    /**
     * Constructs a new Evaluator for the given instance, using a default Options
     * object.
     *
     * @ensures this.instance' = instance && this.options' = new Options()
     * @throws NullPointerException instance = null
     */
    public Evaluator(Instance instance) {
        this(instance, new Options());
    }

    /**
     * Constructs a new Evaluator for the given instance and options
     *
     * @ensures this.instance' = instance && this.options' = options
     * @throws NullPointerException instance = null || options = null
     */
    public Evaluator(Instance instance, Options options) {
        if (instance == null || options == null)
            throw new NullPointerException();
        this.instance = instance;
        this.options = options;
    }

    /**
     * Returns the Options object used by this evaluator.
     *
     * @return this.options
     */
    public Options options() {
        return options;
    }

    /**
     * Returns this.instance. Any modifications to the returned object will be
     * reflected in the behavior of the evaluate methods.
     *
     * @return this.instance
     */
    public Instance instance() {
        return instance;
    }

    /**
     * Evaluates the specified formula with respect to the relation-tuple mappings
     * given by this.instance and using this.options.
     *
     * @return true if formula is true with respect to this.instance and
     *         this.options; otherwise returns false
     * @throws kodkod.engine.fol2sat.HigherOrderDeclException the formula contains a
     *             higher order declaration
     * @throws kodkod.engine.fol2sat.UnboundLeafException the formula contains an
     *             undeclared variable or a relation not mapped by this.instance
     */
    public boolean evaluate(Formula formula) {
        if (formula == null)
            throw new NullPointerException("formula");
        return Translator.evaluate(formula, instance, options).booleanValue();
    }

    /**
     * Evaluates the specified expession with respect to the relation-tuple mappings
     * given by this.instance and using this.options.
     *
     * @return {@link kodkod.instance.TupleSet set} of tuples to which the
     *         expression evaluates given the mappings in this.instance and the
     *         options in this.options.
     * @throws kodkod.engine.fol2sat.HigherOrderDeclException the expression
     *             contains a higher order declaration
     * @throws kodkod.engine.fol2sat.UnboundLeafException the expression contains an
     *             undeclared variable or a relation not mapped by this.instance
     */
    public TupleSet evaluate(Expression expression) {
        if (expression == null)
            throw new NullPointerException("expression");
        final BooleanMatrix sol = Translator.evaluate(expression, instance, options);
        this.wasOverflow = sol.defCond().getAccumOverflow() == BooleanConstant.TRUE;
        return instance.universe().factory().setOf(expression.arity(), sol.denseIndices());
    }

    /**
     * Evaluates the specified int expession with respect to the relation-tuple
     * mappings given by this.instance and using this.options.
     *
     * @return the integer to which the expression evaluates given the mappings in
     *         this.instance and the options in this.options.
     * @throws kodkod.engine.fol2sat.HigherOrderDeclException intExpr contains a
     *             higher order declaration
     * @throws kodkod.engine.fol2sat.UnboundLeafException intExpr contains an
     *             undeclared variable or a relation not mapped by this.instance
     */
    public int evaluate(IntExpression intExpr) {
        if (intExpr == null)
            throw new NullPointerException("intexpression");
        final Int sol = Translator.evaluate(intExpr, instance, options);
        this.wasOverflow = sol.defCond().getAccumOverflow() == BooleanConstant.TRUE;
        return sol.value();
    }

    /**
     * Returns whether overflow was detected during evaluation
     */ // [AM]
    public boolean wasOverflow() {
        return wasOverflow;
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return options + "\n" + instance;
    }
}
