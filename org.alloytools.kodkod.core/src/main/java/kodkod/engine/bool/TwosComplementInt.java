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

import static kodkod.engine.bool.BooleanConstant.FALSE;
import static kodkod.engine.bool.BooleanConstant.TRUE;
import static kodkod.engine.bool.Operator.AND;
import static kodkod.engine.bool.Operator.OR;

import java.util.AbstractList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Variable;
import kodkod.engine.config.Options.OverflowPolicy;
import kodkod.engine.fol2sat.Environment;
import kodkod.util.collections.Containers;

/**
 * Two's complement integer representation. Supports comparisons, addition and
 * subtraction. Integers are represented in little-endian (least significant bit
 * first) order.
 *
 * @author Emina Torlak
 */
@SuppressWarnings("rawtypes" )
final class TwosComplementInt extends Int {

    private final BooleanValue[] bits;

    /**
     * Constructs a TwosComplementInt out of the given factory and bits.
     *
     * @requires bits is well formed
     * @ensures this.factory' = factory && this.bits' = bits
     */
    private TwosComplementInt(BooleanFactory factory, BooleanValue[] bits, BooleanValue overflow, BooleanValue accumOverflow) {
        this(factory, bits, Collections.<Variable> emptySet(), overflow, accumOverflow);
    }

    private TwosComplementInt(BooleanFactory factory, BooleanValue[] bits, Collection<Variable> vars, BooleanValue overflow, BooleanValue accumOverflow) {
        super(factory, vars, true);
        this.bits = bits;
        defCond().setOverflows(overflow, accumOverflow);
    }

    /**
     * Constructs a TwosComplementInt that represents either 0 or the given number,
     * depending on the value of the given bit.
     *
     * @requires factory.encoding = TWOSCOMPLEMENT && bit in factory.components
     * @ensures this.factory' = factory
     * @ensures bits is a two's-complement representation of the given number that
     *          uses the provided bit in place of 1's
     */
    TwosComplementInt(BooleanFactory factory, int number, BooleanValue bit) {
        super(factory, Collections.<Variable> emptySet(), true);
        final int width = bitwidth(number);
        this.bits = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            bits[i] = (number & (1 << i)) == 0 ? FALSE : bit;
        }
        if (factory.noOverflow != OverflowPolicy.NONE && !checkBounds(number)) {
            defCond().setOverflows(TRUE, TRUE);
        }
    }

    /**
     * Checks whether a given integer literal is representable using only
     * <code>this.factory.bitwidth</code> bits.
     */
    private boolean checkBounds(int num) {
        return num >= minInt() && num <= maxInt();
    }

    /**
     * Returns the min int representable using only
     * <code>this.factory.bitwidth</code> bits.
     */
    private int minInt() {
        return -(1 << (factory.bitwidth - 1));
    }

    /**
     * Returns the max int representable using only
     * <code>this.factory.bitwidth</code> bits.
     */
    private int maxInt() {
        return (1 << (factory.bitwidth - 1)) - 1;
    }

    /**
     * ORs overflow circuits of <code>this</code> object (
     * <code>this.mergedOverflow</code>), a given <code>other</code> object (
     * <code>other.mergedOverflow</code>), and a given overflow circuit (
     * <code>of</code>)
     */
    private BooleanValue mergeOverflows(Int other, BooleanValue of) {
        if (factory.noOverflow == OverflowPolicy.NONE)
            return FALSE;
        return DefCond.merge(factory, of, defCond(), other.defCond());
    }

    /**
     * Returns the number of bits needed/allowed to represent the given number.
     *
     * @return the number of bits needed/allowed to represent the given number.
     */
    private int bitwidth(int number) {
        if (number > 0)
            return StrictMath.min(33 - Integer.numberOfLeadingZeros(number), factory.bitwidth);
        else if (number < 0)
            return StrictMath.min(33 - Integer.numberOfLeadingZeros(~number), factory.bitwidth);
        else // number = 0
            return 1;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#isConstant()
     */
    @Override
    public final boolean isConstant() {
        for (int i = width() - 1; i >= 0; i--) {
            BooleanValue b = bit(i);
            if (b != TRUE && b != FALSE)
                return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#twosComplementBits()
     */
    @Override
    public final List<BooleanValue> twosComplementBits() {
        return new AbstractList<BooleanValue>() {

            @Override
            public BooleanValue get(int i) {
                if (i < 0 || i >= factory.bitwidth)
                    throw new IndexOutOfBoundsException();
                return bit(i);
            }

            @Override
            public int size() {
                return factory.bitwidth;
            }
        };
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#width()
     */
    @Override
    public int width() {
        return bits.length;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#value()
     */
    @Override
    public final int value() {
        int ret = 0;
        final int max = bits.length - 1;
        for (int i = 0; i < max; i++) {
            if (bits[i] == TRUE)
                ret += 1 << i;
            else if (bits[i] != FALSE)
                throw new IllegalStateException(this + " is not constant.");
        }
        if (bits[max] == TRUE)
            ret -= 1 << max;
        else if (bits[max] != FALSE)
            throw new IllegalStateException(this + " is not constant.");
        return ret;
    }

    /**
     * Returns the BooleanValue at the specified index.
     *
     * @requires 0 <= i < this.factory.bitwidth
     * @return this.bits[i]
     */
    @Override
    public final BooleanValue bit(int i) {
        return bits[StrictMath.min(i, bits.length - 1)];
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#msb(kodkod.engine.bool.Int)
     */
    @Override
    public final BooleanValue msb() {
        return bits[bits.length - 1];
    }

    /**
     * If overflow checking is disabled returns <code>value</code>. Otherwise,
     * returns a conjunction of <code>value</code>, <code>lhs.accumOverflow</code>,
     * and <code>rhs.accumOverflow</code>. ~~~ NOTE ~~~: Every time a BooleanValue
     * is returned as a result of an operation over Ints, one of the
     * <code>ensureNoOverflow</code> methods should be called.
     */
    private BooleanValue ensureNoOverflow(Environment env, BooleanValue value, Int... ints) {
        IDefCond[] dcs = new IDefCond[ints.length];
        for (int i = 0; i < ints.length; i++)
            dcs[i] = ints[i].defCond();
        return DefCond.ensureDef(factory, env, value, dcs);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#eq(kodkod.engine.bool.Int)
     */
    @Override
    public final BooleanValue eq(Int other, Environment env) {
        BooleanValue ret = eqWithoutOverflow(other);
        return ensureNoOverflow(env, ret, this, other);
    }

    @Override
    public final BooleanValue neq(Int other, Environment env) {
        BooleanValue ret = factory.not(eqWithoutOverflow(other));
        return ensureNoOverflow(env, ret, this, other);
    }

    private BooleanValue eqWithoutOverflow(Int other) {
        validate(other);
        final BooleanAccumulator cmp = BooleanAccumulator.treeGate(AND);
        for (int i = 0, width = StrictMath.max(width(), other.width()); i < width; i++) {
            if (cmp.add(factory.iff(bit(i), other.bit(i))) == FALSE)
                return FALSE;
        }
        BooleanValue ret = factory.accumulate(cmp);
        return ret;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#lt(kodkod.engine.bool.Int)
     */
    @Override
    public final BooleanValue lt(Int other, Environment env) {
        final BooleanValue leq = lte(other);
        final BooleanAccumulator acc = BooleanAccumulator.treeGate(OR);
        for (int i = 0, width = StrictMath.max(width(), other.width()); i < width; i++) {
            acc.add(factory.xor(bit(i), other.bit(i)));
        }
        BooleanValue ret = factory.and(leq, factory.accumulate(acc));
        return ensureNoOverflow(env, ret, this, other);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#lte(kodkod.engine.bool.Int)
     */
    @Override
    public BooleanValue lte(Int other, Environment env) {
        validate(other);
        final BooleanAccumulator cmp = BooleanAccumulator.treeGate(Operator.AND);
        final int last = StrictMath.max(width(), other.width()) - 1;
        cmp.add(factory.implies(other.bit(last), bit(last)));
        BooleanValue prevEquals = factory.iff(bit(last), other.bit(last));
        for (int i = last - 1; i >= 0; i--) {
            BooleanValue v0 = bit(i), v1 = other.bit(i);
            cmp.add(factory.implies(prevEquals, factory.implies(v0, v1)));
            prevEquals = factory.and(prevEquals, factory.iff(v0, v1));
        }
        BooleanValue ret = factory.accumulate(cmp);
        return ensureNoOverflow(env, ret, this, other);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#plus(kodkod.engine.bool.Int)
     */
    @Override
    public Int plus(Int other) {
        validate(other);
        final int width = StrictMath.min(StrictMath.max(width(), other.width()) + 1, factory.bitwidth);
        final BooleanValue[] plus = new BooleanValue[width];
        BooleanValue carry = FALSE;
        BooleanValue c1 = FALSE;
        BooleanValue c2 = FALSE;
        for (int i = 0; i < width; i++) {
            BooleanValue v0 = bit(i), v1 = other.bit(i);
            plus[i] = factory.sum(v0, v1, carry);
            carry = factory.carry(v0, v1, carry);
            if (i == width - 2)
                c2 = carry;
            else if (i == width - 1)
                c1 = carry;
        }
        BooleanValue overflow = FALSE;
        BooleanValue accumOF = FALSE;
        if (width == factory.bitwidth && factory.noOverflow != OverflowPolicy.NONE) {
            overflow = factory.xor(c1, c2);
            accumOF = mergeOverflows(other, overflow);
        }
        return new TwosComplementInt(factory, plus, unionVars(this, other), overflow, accumOF);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#minus(kodkod.engine.bool.Int)
     */
    @Override
    public Int minus(Int other) {
        validate(other);
        final int width = StrictMath.min(StrictMath.max(width(), other.width()) + 1, factory.bitwidth);
        final BooleanValue[] minus = new BooleanValue[width];
        BooleanValue carry = TRUE;
        BooleanValue c1 = FALSE;
        BooleanValue c2 = FALSE;
        for (int i = 0; i < width; i++) {
            BooleanValue v0 = bit(i), v1 = other.bit(i).negation();
            minus[i] = factory.sum(v0, v1, carry);
            carry = factory.carry(v0, v1, carry);
            if (i == width - 2)
                c2 = carry;
            else if (i == width - 1)
                c1 = carry;
        }
        BooleanValue overflow = FALSE;
        BooleanValue accumOF = FALSE;
        if (width == factory.bitwidth && factory.noOverflow != OverflowPolicy.NONE) {
            overflow = factory.xor(c1, c2);
            accumOF = mergeOverflows(other, overflow);
        }
        return new TwosComplementInt(factory, minus, unionVars(this, other), overflow, accumOF);
    }

    /**
     * Adds the newBit and the given carry to this.bits[index] and returns the new
     * carry.
     *
     * @requires 0 <= index < this.width
     * @ensures this.bits'[index] = this.factory.sum(this.bits[index], newBit, cin)
     * @return this.factory.carry(this.bits[index], newBit, cin)
     */
    private BooleanValue addAndCarry(int index, BooleanValue newBit, BooleanValue cin) {
        BooleanValue oldBit = bits[index];
        bits[index] = factory.sum(oldBit, newBit, cin);
        return factory.carry(oldBit, newBit, cin);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#multiply(kodkod.engine.bool.Int)
     */
    // [AM] TODO: not optimal, uses double precision (too many bits)!
    @Override
    public Int multiply(Int other) {
        validate(other);
        final int retWidth = width() + other.width();
        final BooleanValue[] mult = new BooleanValue[retWidth];
        final Set<Variable> unionVars = unionVars(this, other);
        final TwosComplementInt ret = new TwosComplementInt(factory, mult, unionVars, FALSE, FALSE);

        /* first partial sum */
        BooleanValue iBit = bit(0);
        for (int j = 0; j < retWidth; j++) {
            mult[j] = factory.and(iBit, other.bit(j));
        }

        /* intermediate partial sums */
        int last = retWidth - 1;
        for (int i = 1; i < last; i++) {
            iBit = this.bit(i);
            BooleanValue carry = FALSE;
            for (int j = 0; j < retWidth - i; j++) {
                BooleanValue bit = factory.and(iBit, other.bit(j));
                carry = ret.addAndCarry(i + j, bit, carry);
            }
        }

        /*
         * last partial sum is subtracted (see
         * http://en.wikipedia.org/wiki/Multiplication_ALU)
         */
        iBit = this.bit(last);
        BooleanValue carry = TRUE;
        for (int j = 0; j < retWidth - last; j++) {
            BooleanValue bit = factory.and(iBit, other.bit(j)).negation();
            carry = ret.addAndCarry(last + j, bit, carry);
        }

        final int width = StrictMath.min(mult.length, factory.bitwidth);
        final BooleanValue[] multTrunc = new BooleanValue[width];
        for (int i = 0; i < multTrunc.length; i++)
            multTrunc[i] = mult[i];

        BooleanValue overflow = FALSE;
        BooleanValue accumOF = FALSE;
        if (factory.noOverflow != OverflowPolicy.NONE) {
            BooleanAccumulator acc = BooleanAccumulator.treeGate(Operator.OR);
            for (int i = multTrunc.length; i < mult.length; i++) {
                acc.add(factory.xor(mult[i - 1], mult[i]));
            }
            overflow = factory.accumulate(acc);
            accumOF = mergeOverflows(other, overflow);
        }
        return new TwosComplementInt(factory, multTrunc, unionVars, overflow, accumOF);
    }

    // @Override
    public Int multiply_no_overflow_detection(Int other) {
        validate(other);
        final int width = StrictMath.min(width() + other.width(), factory.bitwidth);
        final BooleanValue[] mult = new BooleanValue[width];
        final TwosComplementInt ret = new TwosComplementInt(factory, mult, unionVars(this, other), FALSE, FALSE);

        /* first partial sum */
        BooleanValue iBit = bit(0), carry;
        for (int j = 0; j < width; j++) {
            mult[j] = factory.and(iBit, other.bit(j));
        }

        final int last = width - 1;
        /* intermediate partial sums */
        for (int i = 1; i < last; i++) {
            carry = FALSE;
            iBit = bit(i);
            for (int j = 0, jmax = width - i; j < jmax; j++) {
                carry = ret.addAndCarry(j + i, factory.and(iBit, other.bit(j)), carry);
            }
        }

        /*
         * last partial sum is subtracted (see
         * http://en.wikipedia.org/wiki/Multiplication_ALU)
         */
        ret.addAndCarry(last, factory.and(this.bit(last), other.bit(0)).negation(), TRUE);
        return ret;
    }

    /**
     * Returns an array of BooleanValues that represents the same integer as this,
     * but using extwidth bits.
     *
     * @requires extwidth >= this.width()
     * @return an array of BooleanValues that represents the same integer as this,
     *         but using extwidth bits.
     */
    private BooleanValue[] extend(int extwidth) {
        final BooleanValue[] ext = new BooleanValue[extwidth];
        final int width = width();
        for (int i = 0; i < width; i++) {
            ext[i] = bits[i];
        }
        final BooleanValue sign = bits[width - 1];
        for (int i = width; i < extwidth; i++) {
            ext[i] = sign;
        }
        return ext;
    }

    /**
     * Performs non-restoring signed division of this and the given integer. Returns
     * the this.factory.bitwidth low-order bits of the quotient if the quotient flag
     * is true; otherwise returns the this.factory.bitwidth low-order bits of the
     * remainder. Both the quotionent and the remainder are given in little endian
     * format.
     *
     * @see Behrooz Parhami, Computer Arithmetic: Algorithms and Hardware Designs,
     *      Oxford University Press, 2000, pp. 218-221.
     * @requires this.factory = d.factory && d instanceof BinaryInt
     * @return an array of boolean values, as described above
     */
    private BooleanValue[] nonRestoringDivision(Int d, boolean quotient) {
        final int width = factory.bitwidth, extended = width * 2 + 1;

        // extend the dividend to bitwidth*2 + 1 and store it in s; the quotient
        // will have width digits
        final BooleanValue[] s = this.extend(extended), q = new BooleanValue[width];

        // detects if one of the intermediate remainders is zero
        final BooleanValue[] svalues = new BooleanValue[width];

        BooleanValue carry, sbit, qbit, dbit;

        // the sign bit of the divisor
        final BooleanValue dMSB = d.bit(width);

        int sleft = 0; // the index which contains the LSB of s
        for (int i = 0; i < width; i++) {
            svalues[i] = factory.accumulate(BooleanAccumulator.treeGate(Operator.OR, s));
            int sright = (sleft + extended - 1) % extended; // the index which
                                                           // contains the MSB
                                                           // of s

            // q[width-i-1] is 1 if sign(s_(i)) = sign(d), otherwise it is 0
            qbit = factory.iff(s[sright], dMSB);
            q[width - i - 1] = qbit;

            // shift s to the left by 1 -- simulated by setting sright to FALSE
            // and sleft to sright
            s[sright] = FALSE;
            sleft = sright;

            // if sign(s_(i)) = sign(d), form s_(i+1) by subtracting (2^width)d
            // from s_(i);
            // otherwise, form s_(i+1) by adding (2^width)d to s_(i).
            carry = qbit;
            for (int di = 0, si = (sleft + width) % extended; di <= width; di++, si = (si + 1) % extended) {
                dbit = factory.xor(qbit, d.bit(di));
                sbit = s[si];
                s[si] = factory.sum(sbit, dbit, carry);
                carry = factory.carry(sbit, dbit, carry);
            }
        }

        // s[0..width] holds the width+1 high order bits of s
        assert (sleft + width) % extended == 0;

        // correction needed if one of the intermediate remainders is zero
        // or s is non-zero and its sign differs from the sign of the dividend
        final BooleanValue incorrect = factory.or(factory.not(factory.accumulate(BooleanAccumulator.treeGate(Operator.AND, svalues))), factory.and(factory.xor(s[width], this.bit(width)), factory.accumulate(BooleanAccumulator.treeGate(Operator.OR, s))));
        final BooleanValue corrector = factory.iff(s[width], d.bit(width));

        if (quotient) { // convert q to 2's complement, correct it if s is
                       // nonzero, and return

            // convert q to 2's complement: shift to the left by 1 and set LSB
            // to TRUE
            System.arraycopy(q, 0, q, 1, width - 1);
            q[0] = TRUE;

            // correct if incorrect evaluates to true as follows: if corrector
            // evaluates to true,
            // increment q; otherwise decrement q.
            final BooleanValue sign = factory.and(incorrect, factory.not(corrector));
            carry = factory.and(incorrect, corrector);

            for (int i = 0; i < width; i++) {
                qbit = q[i];
                q[i] = factory.sum(qbit, sign, carry);
                carry = factory.carry(qbit, sign, carry);
            }

            return q;
        } else { // correct s if non-zero and return

            // correct if incorrect evaluates to true as follows: if corrector
            // evaluates to true,
            // subtract (2^width)d from s; otherwise add (2^width)d to s
            carry = factory.and(incorrect, corrector);

            for (int i = 0; i <= width; i++) {
                dbit = factory.and(incorrect, factory.xor(corrector, d.bit(i)));
                sbit = s[i];
                s[i] = factory.sum(sbit, dbit, carry);
                carry = factory.carry(sbit, dbit, carry);
            }

            final BooleanValue[] r = new BooleanValue[width];
            System.arraycopy(s, 0, r, 0, width);
            return r;
        }

    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#divide(kodkod.engine.bool.Int)
     */
    @Override
    public Int divide(Int other) {
        validate(other);
        TwosComplementInt ret = new TwosComplementInt(factory, nonRestoringDivision(other, true), unionVars(this, other), FALSE, FALSE);
        BooleanValue divByZero = other.eq(factory.integer(0));
        BooleanValue singleOverflowCase = factory.and(this.eq(factory.integer(-(1 << (factory.bitwidth - 1)))), other.eq(factory.integer(-1)));
        BooleanValue overflow = factory.or(divByZero, singleOverflowCase);
        BooleanValue accumOF = mergeOverflows(other, overflow);
        ret.defCond().setOverflows(overflow, accumOF);
        return ret;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#modulo(kodkod.engine.bool.Int)
     */
    @Override
    public Int modulo(Int other) {
        validate(other);
        TwosComplementInt ret = new TwosComplementInt(factory, nonRestoringDivision(other, false), unionVars(this, other), FALSE, FALSE);
        BooleanValue divByZero = other.eq(factory.integer(0));
        BooleanValue accumOF = mergeOverflows(other, divByZero);
        ret.defCond().setOverflows(FALSE, accumOF);
        return ret;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#choice(kodkod.engine.bool.BooleanValue,
     *      kodkod.engine.bool.Int)
     */
    @Override
    public Int choice(BooleanValue condition, Int other) {
        validate(other);
        final int width = StrictMath.max(width(), other.width());
        final BooleanValue[] choice = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            choice[i] = factory.ite(condition, bit(i), other.bit(i));
        }
        BooleanValue of = factory.ite(condition, defCond().getOverflow(), other.defCond().getOverflow());
        BooleanValue accumOF = factory.ite(condition, defCond().getAccumOverflow(), other.defCond().getAccumOverflow());
        return new TwosComplementInt(factory, choice, unionVars(this, other), of, accumOF);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#and(kodkod.engine.bool.Int)
     */
    @Override
    public Int and(Int other) {
        validate(other);
        final int width = StrictMath.max(width(), other.width());
        final BooleanValue[] and = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            and[i] = factory.and(bit(i), other.bit(i));
        }
        Set<Variable> unionVars = unionVars(this, other);
        return new TwosComplementInt(factory, and, unionVars, FALSE, mergeOverflows(other, FALSE));
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#or(kodkod.engine.bool.Int)
     */
    @Override
    public Int or(Int other) {
        validate(other);
        final int width = StrictMath.max(width(), other.width());
        final BooleanValue[] or = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            or[i] = factory.or(bit(i), other.bit(i));
        }
        return new TwosComplementInt(factory, or, unionVars(this, other), FALSE, mergeOverflows(other, FALSE));
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#xor(kodkod.engine.bool.Int)
     */
    @Override
    public Int xor(Int other) {
        validate(other);
        final int width = StrictMath.max(width(), other.width());
        final BooleanValue[] xor = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            xor[i] = factory.xor(bit(i), other.bit(i));
        }
        return new TwosComplementInt(factory, xor, unionVars(this, other), FALSE, mergeOverflows(other, FALSE));
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#shl(kodkod.engine.bool.Int)
     */
    @Override
    public Int shl(Int other) {
        validate(other);
        final int width = factory.bitwidth;
        final TwosComplementInt shifted = new TwosComplementInt(factory, extend(width), unionVars(this, other), FALSE, FALSE);
        final int max = 32 - Integer.numberOfLeadingZeros(width - 1);
        BooleanAccumulator acc = BooleanAccumulator.treeGate(Operator.OR);
        for (int i = 0; i < width; i++) {
            int shift = 1 << i;
            BooleanValue bit = other.bit(i);
            // overflow: check if the bits being pushed out is different from
            // the one immediately to the right of it
            for (int x = 0; x < shift; x++) {
                BooleanValue b1 = width - x - 1 < 0 ? FALSE : shifted.bit(width - x - 1);
                BooleanValue b2 = width - x - 2 < 0 ? FALSE : shifted.bit(width - x - 2);
                if (factory.noOverflow != OverflowPolicy.NONE)
                    acc.add(factory.ite(bit, factory.xor(b1, b2), FALSE));
            }
            if (i < max) {
                for (int j = width - 1; j >= 0; j--) {
                    shifted.bits[j] = factory.ite(bit, j < shift ? FALSE : shifted.bit(j - shift), shifted.bits[j]);
                }
            }
        }
        if (factory.noOverflow != OverflowPolicy.NONE) {
            BooleanValue overflow = factory.accumulate(acc);
            BooleanValue accumOF = mergeOverflows(other, overflow);
            shifted.defCond().setOverflows(overflow, accumOF);
        }
        return shifted;
    }

    /**
     * Performs a right shift with the given extension.
     */
    private Int shr(Int other, BooleanValue sign) {
        validate(other);
        final int width = factory.bitwidth;
        final TwosComplementInt shifted = new TwosComplementInt(factory, extend(width), unionVars(this, other), FALSE, FALSE);
        final int max = 32 - Integer.numberOfLeadingZeros(width - 1);
        for (int i = 0; i < max; i++) {
            int shift = 1 << i;
            int fill = width - shift;
            BooleanValue bit = other.bit(i);
            for (int j = 0; j < width; j++) {
                shifted.bits[j] = factory.ite(bit, j < fill ? shifted.bit(j + shift) : sign, shifted.bits[j]);
            }
        }
        shifted.defCond().setOverflows(FALSE, mergeOverflows(other, FALSE));
        return shifted;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#shr(kodkod.engine.bool.Int)
     */
    @Override
    public Int shr(Int other) {
        return shr(other, FALSE);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#sha(kodkod.engine.bool.Int)
     */
    @Override
    public Int sha(Int other) {
        return shr(other, bits[bits.length - 1]);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#negate()
     */
    @Override
    public Int negate() {
        return (new TwosComplementInt(factory, new BooleanValue[] {
                                                                   FALSE
        }, FALSE, FALSE)).minus(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#not()
     */
    @Override
    public Int not() {
        final int width = width();
        final BooleanValue[] inverse = new BooleanValue[width];
        for (int i = 0; i < width; i++) {
            inverse[i] = factory.not(bits[i]);
        }
        return new TwosComplementInt(factory, inverse, defCond().vars(), FALSE, defCond().getAccumOverflow());
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#abs()
     */
    @Override
    public Int abs() {
        Int negated = negate();
        return choice(factory.not(bits[bits.length - 1]), negated);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#sgn()
     */
    @Override
    public Int sgn() {
        final BooleanValue[] sgn = new BooleanValue[2];
        sgn[0] = factory.accumulate(BooleanAccumulator.treeGate(Operator.OR, bits));
        sgn[1] = bits[bits.length - 1];
        return new TwosComplementInt(factory, sgn, defCond().vars(), FALSE, defCond().getAccumOverflow());
    }

    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "b" + Arrays.toString(bits);
    }

    /**
     * If the plus flag is true, returns a sum of this and other ints, with a
     * cascade of adders or logarithmic depth. If the plus flag is false, returns a
     * product of this and other ints, with a cascade of multipliers of logarithmic
     * depth.
     *
     * @return plus => PLUS(this, others) else MULTIPLY(this, others)
     */
    private Int apply(boolean plus, Int... others) {
        final Int[] ints = Containers.copy(others, 0, new Int[others.length + 1], 1, others.length);
        ints[0] = this;
        for (int part = ints.length; part > 1; part -= part / 2) {
            final int max = part - 1;
            for (int i = 0; i < max; i += 2) {
                ints[i / 2] = plus ? ints[i].plus(ints[i + 1]) : ints[i].multiply(ints[i + 1]);
            }
            if (max % 2 == 0) { // even max => odd number of entries
                ints[max / 2] = ints[max];
            }
        }
        return ints[0];
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#plus(kodkod.engine.bool.Int[])
     */
    @Override
    public Int plus(Int... others) {
        return apply(true, others);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#multiply(kodkod.engine.bool.Int[])
     */
    @Override
    public Int multiply(Int... others) {
        return apply(false, others);
    }

    /**
     * Applies the given nary operator to this and the given ints.
     *
     * @return op(this, others)
     */
    private Int apply(Operator.Nary op, Int... others) {
        int width = width();
        for (Int other : others) {
            validate(other);
            width = Math.max(width, other.width());
        }
        final BooleanValue[] bits = new BooleanValue[width];
        final BooleanValue shortCircuit = op.shortCircuit();
        for (int i = 0; i < width; i++) {
            final BooleanAccumulator acc = BooleanAccumulator.treeGate(op, bit(i));
            for (Int other : others) {
                if (acc.add(other.bit(i)) == shortCircuit)
                    break;
            }
            bits[i] = factory.accumulate(acc);
        }

        final BooleanValue[] allOverflows = new BooleanValue[others.length + 1];
        final Set<Variable> allVars = new HashSet<Variable>();
        allOverflows[0] = defCond().getAccumOverflow();
        allVars.addAll(defCond().vars());
        for (int i = 1; i < allOverflows.length; i++) {
            allOverflows[i] = others[i - 1].defCond().getAccumOverflow();
            allVars.addAll(others[i - 1].defCond().vars());
        }
        BooleanAccumulator overflowAcc = BooleanAccumulator.treeGate(op, allOverflows);
        return new TwosComplementInt(factory, bits, allVars, FALSE, factory.accumulate(overflowAcc));
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#and(kodkod.engine.bool.Int[])
     */
    @Override
    public Int and(Int... others) {
        return apply(AND, others);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.bool.Int#or(kodkod.engine.bool.Int[])
     */
    @Override
    public Int or(Int... others) {
        return apply(OR, others);
    }

    private static Set<Variable> emptyVars = Collections.unmodifiableSet(new HashSet<Variable>());

    private Set<Variable> unionVars(Int int1, Int int2) {
        if (factory.noOverflow == OverflowPolicy.NONE)
            return emptyVars;
        Set<Variable> union = new HashSet<Variable>();
        union.addAll(int1.defCond().vars());
        union.addAll(int2.defCond().vars());
        return union;
    }
}
