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
package kodkod.engine.bool;

import static kodkod.engine.bool.Operator.AND;
import static kodkod.engine.bool.Operator.OR;

import java.util.Collection;
import java.util.Iterator;

import kodkod.engine.config.Options;
import kodkod.engine.config.Options.IntEncoding;
import kodkod.engine.config.Options.OverflowPolicy;
import kodkod.util.ints.IntSet;

/**
 * A factory for creating {@link kodkod.engine.bool.BooleanValue boolean
 * values}, {@link kodkod.engine.bool.BooleanMatrix matrices}, and
 * {@link kodkod.engine.bool.Int ints}.
 *
 * @specfield comparisonDepth: int // the depth to which circuits should be
 *            checked for equality
 * @specfield intEncoding: {@link IntEncoding} // the encoding used for
 *            generating integers ({@link #integer(int)}
 * @specfield bitwidth: int // the bitwidth used for integer computations
 * @specfield components: set {@link BooleanValue}
 * @invariant {@link BooleanConstant} in components
 * @invariant no f1, f2: BooleanFactory | f1 != f2 => f1.components &
 *            f2.components = {@link BooleanConstant}
 * @invariant let formulas = (components & {@link BooleanFormula}) -
 *            {@link NotGate} | min(formulas.label) = 1 && max(formulas.label) =
 *            #formulas
 * @author Emina Torlak
 */
public abstract class BooleanFactory {

    /**
     * A circuit factory used internally to assemble circuits.
     */
    private final CBCFactory circuits;

    private int              numVars;

    /** The bitwidth used for integer computations */
    final int                bitwidth;

    /** Whether or not it should forbid overflows */ // [AM]
    final OverflowPolicy     noOverflow;

    /**
     * Constructs a boolean factory with the given number of input variables. Gates
     * are checked for semantic equality down to the given depth. Integers are
     * represented using the given number of bits. The noOverflow bit tells whether
     * or not to forbid overflows.
     *
     * @requires 0 <= numVars < Integer.MAX_VALUE
     * @requires checkToDepth >= 0 && bitwidth > 0
     * @ensures #this.components' = numInputVariables && this.components' in
     *          BooleanVariable
     * @ensures this.bitwidth' = bitwidth
     * @ensures this.comparisonDepth' = comparisonDepth
     */
    private BooleanFactory(int numVars, int comparisonDepth, int bitwidth, OverflowPolicy overflowPolicy) {
        this.circuits = new CBCFactory(numVars, 1 << comparisonDepth);
        this.bitwidth = bitwidth;
        this.numVars = numVars;
        this.noOverflow = overflowPolicy;
    }

    /**
     * Returns a boolean factory, initialized to contain the given number of boolean
     * variables.
     * <p>
     * Gates are checked for semantic equality down to the depth given by
     * options.sharing when checking for cached values. In general, setting the
     * comparison depth to a higher value will result in more subcomponents being
     * shared. However, it will also slow down gate construction.
     * </p>
     * <p>
     * Integers are created/manipulated according to the specifications in the given
     * Options object.
     * </p>
     *
     * @return {f: BooleanFactory | #(f.components & BooleanVariable) = numVars &&
     *         BooleanConstant in f.components && f.components in BooleanVariable +
     *         BooleanConstant && f.comparisonDepth = options.sharing && f.bitwidth
     *         = options.bitwidth && f.intEncoding = options.intEncoding && (all i:
     *         [1..numVars] | one f.components.label & i }}
     * @throws IllegalArgumentException numVars < 0 || numVars = Integer.MAX_VALUE
     * @throws NullPointerException options = null
     */
    public static BooleanFactory factory(int numVars, Options options) {
        switch (options.intEncoding()) {
            case TWOSCOMPLEMENT :
                return new TwosComplementFactory(numVars, options.sharing(), options.bitwidth(), options.overflowPolicy());
            default :
                throw new IllegalArgumentException("unknown encoding: " + options.intEncoding());
        }
    }

    /**
     * Returns a BooleanFactory with no variables; the returned factory can
     * manipulate only constants.
     *
     * @return {f: BooleanFactory | f.components = BooleanConstant &&
     *         f.comparisonDepth = options.sharing && f.bitwidth = options.bitwidth
     *         && f.intEncoding = options.intEncoding }
     * @throws NullPointerException options = null
     */
    public static BooleanFactory constantFactory(Options options) {
        return factory(0, options);
    }

    /**
     * Returns the depth (from the root) to which components are checked for
     * semantic equality during gate construction.
     *
     * @return this.comparisonDepth
     */
    public final int comparisonDepth() {
        return Integer.numberOfTrailingZeros(circuits.cmpMax());
    }

    /**
     * Sets the comparison depth to the given value. Setting the comparison depth to
     * a high value will result in more subcomponents being shared. However, it will
     * also slow down gate construction.
     *
     * @ensures this.comparisonDepth' = newDepth
     * @throws IllegalArgumentException newDepth < 1
     */
    public final void setComparisonDepth(int newDepth) {
        if (newDepth < 1)
            throw new IllegalArgumentException("newDepth < 1: " + newDepth);
        circuits.setCmpMax(1 << newDepth);
    }

    /**
     * Returns the bitwidth used for integer representation.
     *
     * @return this.bitwidth
     */
    public final int bitwidth() {
        return bitwidth;
    }

    /** Returns the noOverflow flag */ // [AM]
    public final OverflowPolicy noOverflow() {
        return noOverflow;
    }

    /**
     * Returns the encoding used by this factory to represent integers.
     *
     * @return this.intEncoding
     */
    public abstract Options.IntEncoding intEncoding();

    /**
     * Returns true if v is in this.components.
     *
     * @return v in this.components
     * @throws NullPointerException v = null
     */
    public final boolean contains(BooleanValue v) {
        return circuits.canAssemble(v);
    }

    /**
     * Returns the maximum label of a {@link BooleanVariable variable} in
     * {@code this.components}.
     *
     * @return max((this.components & BooleanVariable).label)
     */
    public final int maxVariable() {
        return circuits.maxVariable();
    }

    /**
     * Returns the maximum label of a {@link BooleanFormula formula} in
     * {@code this.components}. Note that {@link #maxFormula()} >=
     * {@link #maxVariable()} since variables themselves are formulas.
     *
     * @return max((this.components & BooleanFormula).label)
     */
    public final int maxFormula() {
        return circuits.maxFormula();
    }

    /**
     * Returns the variable with the given label.
     *
     * @requires 0 < label <= numberOfVariables()
     * @return (this.components & BooleanVariable).label
     */
    public final BooleanVariable variable(int label) {
        return circuits.variable(label);
    }

    /**
     * Adds the specified number of fresh variables to {@code this.components}.
     *
     * @requires numVars >= 0
     * @ensures let diff = this.components' - this.components | diff in
     *          BooleanVariable && #diff = numVars && diff.label = { i: int |
     *          this.maxFormula() < i <= this.maxFormula() + numVars }
     */
    public final void addVariables(int numVars) {
        if (numVars < 0) {
            throw new IllegalArgumentException("Expected numVars >= 0, given numVars = " + numVars);
        } else if (numVars > 0) {
            circuits.addVariables(numVars);
            this.numVars += numVars;
        } // else do nothing
    }

    /**
     * Returns the number of variables in this factory.
     *
     * @return #(this.components & BooleanVariable)
     */
    public final int numberOfVariables() {
        return numVars;
    }

    /**
     * Returns the negation of the given boolean value.
     *
     * @return {n: BooleanValue | n.label = -v.label && [[n]] = ![[v]] }
     * @ensures (components.v).components' = (components.v).components + n
     * @throws NullPointerException v = null
     */
    public final BooleanValue not(BooleanValue v) {
        return v.negation();
    }

    /**
     * Returns a boolean value whose meaning is the conjunction of the input
     * components. The behavior of this method is unspecified if v0 or v1 are not
     * components of this factory.
     *
     * @requires v0 + v1 in this.components
     * @return {v: BooleanValue | [[v]] = [[v0]] AND [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue and(BooleanValue v0, BooleanValue v1) {
        return circuits.assemble(AND, v0, v1);
    }

    /**
     * Returns a boolean value whose meaning is the disjunction of the input
     * components. The behavior of this method is unspecified if v0 or v1 are not
     * components of this factory.
     *
     * @requires v0 + v1 in this.components
     * @return {v: BooleanValue | [[v]] = [[v0]] OR [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     * @throws IllegalArgumentException v0 + v1 !in this.components
     */
    public final BooleanValue or(BooleanValue v0, BooleanValue v1) {
        return circuits.assemble(OR, v0, v1);
    }

    /**
     * Returns a boolean value whose meaning is [[v0]] ^ [[v1]]. The behavior of
     * this method is unspecified if v0 or v1 are not components of this factory.
     *
     * @requires v0 + v1 in this.components
     * @return { v: BooleanValue | [[v]] = [[v0]] xor [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue xor(BooleanValue v0, BooleanValue v1) {
        return circuits.assemble(v0, v1.negation(), v1);
    }

    /**
     * Returns a boolean value whose meaning is [[v0]] => [[v1]]. The behavior of
     * this method is unspecified if v0 or v1 are not components of this factory.
     *
     * @requires v0 + v1 in this.components
     * @return { v: BooleanValue | [[v]] = [[v0]] => [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue implies(BooleanValue v0, BooleanValue v1) {
        return circuits.assemble(OR, v0.negation(), v1);
    }

    /**
     * Returns a boolean value whose meaning is [[v0]] <=> [[v1]]. The behavior of
     * this method is unspecified if v0 or v1 are not components of this factory.
     *
     * @requires v0 + v1 in this.components
     * @return { v: BooleanValue | [[v]] = [[v0]] iff [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue iff(BooleanValue v0, BooleanValue v1) {
        return circuits.assemble(v0, v1, v1.negation());
    }

    /**
     * Returns a boolean value whose meaning is [[i]] ? [[t]] : [[e]]. The behavior
     * of this method is unspecified if i, t, or e are not components of this
     * factory.
     *
     * @requires i + t + e in this.components
     * @return { v: BooleanValue | [[v]] = [[i]] ? [[t]] : [[e]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue ite(BooleanValue i, BooleanValue t, BooleanValue e) {
        return circuits.assemble(i, t, e);
    }

    /**
     * Returns a boolean value whose meaning is the sum bit of a full binary adder.
     * The behavior of this method is unspecified if v0, v1, or cin are not
     * components of this factory.
     *
     * @requires v0 + v1 + cin in this.components
     * @return { v: BooleanValue | [[v]] = [[cin]] xor [[v0]] xor [[v1]] }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue sum(BooleanValue v0, BooleanValue v1, BooleanValue cin) {
        return xor(cin, xor(v0, v1));
    }

    /**
     * Returns a boolean value whose meaning is the carry out bit of a full binary
     * adder. The behavior of this method is unspecified if v0, v1, or cin are not
     * components of this factory.
     *
     * @requires v0 + v1 + cin in this.components
     * @return { v: BooleanValue | [[v]] = ([[v0]] and [[v1]]) or ([[cin]] and
     *         ([[v0]] xor [[v1]])) }
     * @ensures this.components' = this.components + v
     * @throws NullPointerException any of the arguments are null
     */
    public final BooleanValue carry(BooleanValue v0, BooleanValue v1, BooleanValue cin) {
        return or(and(v0, v1), and(cin, xor(v0, v1)));
    }

    /**
     * Converts the given accumulator into an immutable boolean value and adds it to
     * this.components. This method requires that all of g's inputs are in
     * this.components. If g has no inputs, its operator's identity constant is
     * returned. If g has one input, that input is returned. Otherwise, an immutable
     * value that is semantically equivalent to g is returned. The behavior of this
     * method is unspecified if the components of g are not components of this
     * factory.
     *
     * @requires g.components in this.components
     * @return no g.inputs => g.op.identity(), one g.inputs => g.inputs, {g' :
     *         BooleanValue - BooleanAccumulator | [[g']] = [[g]] }
     * @ensures this.components' = this.components + g'
     */
    public final BooleanValue accumulate(BooleanAccumulator g) {
        return circuits.assemble(g);
    }

    /**
     * Returns an Int that represents the given number using this.intEncoding.
     *
     * @return { i: Int | [[i]] = number && i.encoding && this.intEncoding &&
     *         i.factory = this}
     * @throws IllegalArgumentException the number cannot be represented using the
     *             specified encoding
     */
    public abstract Int integer(int number);

    /**
     * Returns an Int that represents 0 or the given number, depending on the value
     * of the given bit. The behavior of this method is unspecified if the bit is
     * not a component of this factory.
     *
     * @return { i: Int | [[bit]] => [[i]] = number, [[i]] = 0 && i.encoding =
     *         this.intEncoding && i.factory = this}
     */
    public abstract Int integer(int number, BooleanValue bit);

    /**
     * Returns an Int that represents the sum of the elements returned by the
     * iterator, using this.intEncoding.
     *
     * @param lo the first element of the current partial sum. Initial should be 0.
     * @param hi the last element of the current partial sum. Initial should be
     *            size-1, where size is the total number of elements returned by the
     *            iterator.
     * @return an Int that represents the sum of the elements returned by the
     *         iterator, using this.intEncoding.
     */
    private Int sum(Iterator<BooleanValue> values, int low, int high) {
        if (low > high)
            return integer(0);
        else if (low == high)
            return integer(1, values.next());
        else {
            final int mid = (low + high) / 2;
            final Int lsum = sum(values, low, mid);
            final Int hsum = sum(values, mid + 1, high);
            return lsum.plus(hsum);
        }
    }

    /**
     * Returns an Int that represents the sum of all values in the given collection.
     *
     * @return an Int that represents the sum of all values in the given collection.
     */
    public final Int sum(Collection<BooleanValue> bits) {
        return sum(bits.iterator(), 0, bits.size() - 1);
    }

    /**
     * Returns a BooleanMatrix with the given dimensions and this as the factory for
     * its non-FALSE components. The returned matrix can store any value from
     * this.components at all indices between 0, inclusive, and d.capacity(),
     * exclusive.
     *
     * @throws NullPointerException d = null
     * @return { m: BooleanMatrix | m.factory = this && m.dimensions = d &&
     *         m.elements = [0..d.capacity) -> one FALSE }
     */
    public final BooleanMatrix matrix(Dimensions d) {
        if (d == null)
            throw new NullPointerException();
        return new BooleanMatrix(d, this);
    }

    /**
     * @throws IllegalArgumentException indices !in [0..d.capacity())
     */
    private static void validate(IntSet indices, Dimensions d) {
        if (!indices.isEmpty()) {
            if (!d.validate(indices.min()) || !d.validate(indices.max()))
                throw new IllegalArgumentException();
        }
    }

    /**
     * Returns a BooleanMatrix <tt>m</tt> with the given dimensions, this as its
     * factory, and the indices from the set <tt>trueIndices</tt> initialized to
     * TRUE. An IndexOutOfBoundsException may be thrown if
     * {@link BooleanMatrix#set(int, BooleanValue)} is called on <tt>m</tt> with an
     * index not contained in <tt>allIndices</tt>. If
     * <tt>allIndices.equals(trueIndices)</tt>, <tt>m</tt> may be a constant matrix;
     * that is, an IllegalArgumentException may be thrown if
     * {@link BooleanMatrix#set(int, BooleanValue)} is called on <tt>m</tt> with a
     * non-constant value. Finally, if cloning <tt>trueIndices</tt> results in an
     * immutable set, then {@link BooleanMatrix#set(int, BooleanValue) m.set(int,
     * BooleanValue)} may throw an UnsupportedOperationException when called with a
     * member of <tt>trueIndices</tt>.
     *
     * @requires allIndices.containsAll(trueIndices)
     * @return { m: BooleanMatrix | m.factory = this && m.dimensions = dims &&
     *         m.elements = [0..d.capacity()-1] ->one FALSE ++ indices->TRUE }
     * @throws IllegalArgumentException allIndices !in [0..d.capacity())
     * @throws IllegalArgumentException one of the input sets is not cloneable
     * @throws NullPointerException d = null || allIndices = null || trueIndices =
     *             null
     */
    public final BooleanMatrix matrix(Dimensions d, IntSet allIndices, IntSet trueIndices) {
        assert allIndices.size() >= trueIndices.size(); // sanity check
        validate(allIndices, d);
        validate(trueIndices, d);
        try {
            return new BooleanMatrix(d, this, allIndices, trueIndices.clone());
        } catch (CloneNotSupportedException e) {
            throw new IllegalArgumentException();
        }

    }

    /**
     * BooleanFactory that produces TwosComplementInts.
     *
     * @invariant encoding = TwosComplement
     * @author Emina Torlak
     */
    private static final class TwosComplementFactory extends BooleanFactory {

        /**
         * Constructs a boolean factory with the given number of input variables. Gates
         * are checked for semantic equality down to the given depth. Integers are
         * represented using the given number of bits.
         *
         * @requires 0 <= numVars < Integer.MAX_VALUE
         * @requires checkToDepth >= 0 && bitwidth > 0
         * @ensures #this.components' = numInputVariables && this.components' in
         *          BooleanVariable
         * @ensures this.bitwidth' = bitwidth
         * @ensures this.comparisonDepth' = comparisonDepth
         * @ensures this.intEncoding' = BINARY
         */
        TwosComplementFactory(int numVars, int comparisonDepth, int bitwidth, OverflowPolicy ofPolicy) {
            super(numVars, comparisonDepth, bitwidth, ofPolicy);
        }

        /**
         * Returns TWOSCOMPLEMENT.
         *
         * @return TWOSCOMPLEMENT
         * @see kodkod.engine.bool.BooleanFactory#intEncoding()
         */
        @Override
        public IntEncoding intEncoding() {
            return IntEncoding.TWOSCOMPLEMENT;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.bool.BooleanFactory#integer(int)
         */
        @Override
        public Int integer(int number) {
            return new TwosComplementInt(this, number, BooleanConstant.TRUE);
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.engine.bool.BooleanFactory#integer(int,
         *      kodkod.engine.bool.BooleanValue)
         */
        @Override
        public Int integer(int number, BooleanValue bit) {
            return new TwosComplementInt(this, number, bit);
        }

    }
}
