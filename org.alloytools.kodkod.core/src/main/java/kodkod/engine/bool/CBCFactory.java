
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
import static kodkod.engine.bool.Operator.CONST;
import static kodkod.engine.bool.Operator.ITE;
import static kodkod.engine.bool.Operator.NOT;
import static kodkod.engine.bool.Operator.OR;
import static kodkod.engine.bool.Operator.VAR;

import java.util.Iterator;
import java.util.Set;

import kodkod.ast.operator.ExprOperator;
import kodkod.engine.bool.Operator.Nary;
import kodkod.util.collections.CacheSet;
import kodkod.util.collections.IdentityHashSet;

/**
 * A factory for creating variables, multigates, and if-then-else gates.
 *
 * @specfield values: set (BooleanVariable + MultiGate + ITEGate)
 * @specfield cmpMax: int // the maximum number of comparisons made when
 *            comparing circuits for equality
 * @invariant no disj factory, factory' : CircuitFactory | some factory.values &
 *            factory'.values
 * @author Emina Torlak
 */
final class CBCFactory {

    /**
     * Sets used as `scrap paper' for gate comparisons. Its capacity is 2^(depth),
     * where depth is the depth to which gates should be checked for equality.
     */
    private final Set<BooleanFormula>        scrap0, scrap1;
    /**
     * Caches variables. This representation is optimized for infrequent addition of
     * ranges of variables at a time (as opposed to frequent addition of one
     * variable at a time).
     *
     * @invariant all i: [0..vars.length-1], j: [1..vars[i].length-1] |
     *            vars[i][j-1].label = vars[i][j] + 1
     * @invariant all i: [1..vars.length-1] | vars[i][0] >
     *            vars[i-1][vars[i-1].length-1] + 1
     * @invariant vars[0][0].label = 1
     */
    private BooleanVariable[][]              vars;
    /**
     * Caches AND, OR, and ITE gates.
     *
     * @invariant all i: [0..2] | c[i].op.ordinal = i
     */
    private final CacheSet<BooleanFormula>[] cache;
    private int                              label, cmpMax;

    /**
     * Constructs a CircuitFactory using the given max comparison parameter,
     * initialized to contain the given number of variables.
     *
     * @requires cmpMax > 0 && numVars >= 0
     * @ensures #this.values' = numVars && this.values in BooleanVariable
     * @ensures this.cmpMax' = cmpMax
     */
    @SuppressWarnings("unchecked" )
    CBCFactory(int numVars, int cmpMax) {
        assert cmpMax > 0 && numVars >= 0;
        this.cmpMax = cmpMax;
        this.label = numVars + 1;
        if (numVars == 0) {
            vars = new BooleanVariable[0][];
        } else {
            vars = new BooleanVariable[1][numVars];
            for (int i = 0; i < numVars; i++) {
                vars[0][i] = new BooleanVariable(i + 1);
            }
        }
        scrap0 = new IdentityHashSet<BooleanFormula>(cmpMax);
        scrap1 = new IdentityHashSet<BooleanFormula>(cmpMax);
        cache = new CacheSet[] {
                                new CacheSet<BooleanFormula>(), new CacheSet<BooleanFormula>(), new CacheSet<BooleanFormula>()
        };
    }

    /**
     * Returns the cache for gates with the given operator.
     *
     * @requires op in AND + OR + ITE
     * @return cache[op.ordinal]
     */
    private CacheSet<BooleanFormula> opCache(Operator op) {
        return cache[op.ordinal];
    }

    /**
     * Sets this.cmpMax to the given value.
     *
     * @requires cmpMax > 0
     * @ensures this.cmpMax' = cmpMax
     */
    void setCmpMax(int cmpMax) {
        assert cmpMax > 0;
        this.cmpMax = cmpMax;
    }

    /**
     * Returns this.cmpMax.
     *
     * @return this.cmpMax
     */
    int cmpMax() {
        return cmpMax;
    }

    /**
     * Returns true if the given value is a valid argument to one of the
     * <tt>assemble</tt> methods. Otherwise returns false.
     *
     * @return v in this.values + this.values.negation + BooleanConstant
     */
    boolean canAssemble(BooleanValue v) {
        if (v.op() == CONST)
            return true;
        if (v.label() < 0)
            v = v.negation();
        if (v instanceof BooleanVariable) {
            return v == variable(v.label());
        } else {
            final BooleanFormula g = (BooleanFormula) v;
            for (Iterator<BooleanFormula> gates = opCache(g.op()).get(g.hashCode()); gates.hasNext();) {
                if (g == gates.next())
                    return true;
            }
            return false;
        }
    }

    /**
     * Returns the maximum label of a {@link BooleanVariable variable} in
     * {@code this.components}.
     *
     * @return max((this.values & BooleanVariable).label)
     */
    int maxVariable() {
        if (vars.length == 0)
            return 0;
        final BooleanVariable[] last = vars[vars.length - 1];
        return last[last.length - 1].label;
    }

    /**
     * Returns the maximum label of a {@link BooleanFormula formula} in
     * {@code this.components}. Note that {@link #maxFormula()} >=
     * {@link #maxVariable()} since variables themselves are formulas.
     *
     * @return max((this.values & BooleanFormula).label)
     */
    int maxFormula() {
        return label - 1;
    }

    /**
     * Returns the boolean variable from this.values with the given label.
     *
     * @requires label in (this.values & BooleanVariable).label
     * @return (this.values & BooleanVariable).label
     */
    BooleanVariable variable(int label) {
        int high = vars.length - 1;
        if (high == 0)
            return vars[0][label - 1];
        int low = 0;
        while (low <= high) {
            final int mid = (low + high) >>> 1;
            final BooleanVariable[] midVars = vars[mid];
            final int midKeyLow = midVars[0].label, midKeyHigh = midKeyLow + midVars.length - 1;
            if (midKeyHigh < label) {
                low = mid + 1;
            } else if (midKeyLow > label) {
                high = mid - 1;
            } else { // variable range found
                return midVars[label - midKeyLow];
            }
        }
        throw new IllegalArgumentException("Expected a variable label, given label = " + label);
    }

    /**
     * Adds the specified number of fresh variables to {@code this.values}.
     *
     * @requires numVars > 0
     * @ensures let diff = this.values' - this.values | diff in BooleanVariable &&
     *          #diff = numVars && diff.label = { i: int | this.maxFormula() < i <=
     *          this.maxFormula() + numVars }
     */
    void addVariables(int numVars) {
        assert numVars > 0;
        if (label > 1 && maxVariable() == maxFormula()) {
            final BooleanVariable[] last = vars[vars.length - 1];
            final BooleanVariable[] newLast = new BooleanVariable[last.length + numVars];
            System.arraycopy(last, 0, newLast, 0, last.length);
            for (int i = last.length, varLabel = this.label; i < newLast.length; i++, varLabel++)
                newLast[i] = new BooleanVariable(varLabel);
            vars[vars.length - 1] = newLast;
        } else {
            final BooleanVariable[][] newVars = new BooleanVariable[vars.length + 1][];
            System.arraycopy(vars, 0, newVars, 0, vars.length);
            final BooleanVariable[] newLast = new BooleanVariable[numVars];
            for (int i = 0, varLabel = this.label; i < numVars; i++, varLabel++)
                newLast[i] = new BooleanVariable(varLabel);
            newVars[vars.length] = newLast;
            vars = newVars;
        }
        this.label += numVars;
    }

    /**
     * Returns a boolean value whose meaning is (if [[i]] then [[t]] else [[e]]).
     *
     * @requires i + t + e in (this.values + this.values.negation + BooleanConstant)
     * @return v: BooleanValue | [[v]] = if [[i]] then [[t]] else [[e]]
     * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v,
     *          this.values' = this.values
     * @throws NullPointerException any of the arguments are null
     */
    BooleanValue assemble(BooleanValue i, BooleanValue t, BooleanValue e) {
        if (i == TRUE || t == e)
            return t;
        else if (i == FALSE)
            return e;
        else if (t == TRUE || i == t)
            return assemble(OR, i, e);
        else if (t == FALSE || i.label() == -t.label())
            return assemble(AND, i.negation(), e);
        else if (e == TRUE || i.label() == -e.label())
            return assemble(OR, i.negation(), t);
        else if (e == FALSE || i == e)
            return assemble(AND, i, t);
        else {
            final BooleanFormula f0 = (BooleanFormula) i, f1 = (BooleanFormula) t, f2 = (BooleanFormula) e;
            final int hash = ITE.hash(f0, f1, f2);

            for (Iterator<BooleanFormula> gates = opCache(ITE).get(hash); gates.hasNext();) {
                BooleanFormula gate = gates.next();
                if (gate.input(0) == i && gate.input(1) == t && gate.input(2) == e)
                    return gate;
            }
            final BooleanFormula ret = new ITEGate(label++, hash, f0, f1, f2);
            opCache(ITE).add(ret);
            return ret;
        }
    }

    /**
     * Returns a boolean value whose meaning is ([[v0]] op [[v1]]).
     *
     * @requires v0 + v1 in (this.values + this.values.negation + BooleanConstant)
     * @return v: BooleanValue | [[v]] = [[v0]] op [[v1]]
     * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v,
     *          this.values' = this.values
     * @throws NullPointerException any of the arguments are null
     */
    BooleanValue assemble(Operator.Nary op, BooleanValue v0, BooleanValue v1) {
        final BooleanValue l, h;
        if (v0.op().ordinal < v1.op().ordinal) {
            l = v0;
            h = v1;
        } else {
            l = v1;
            h = v0;
        }
        if (h.op() == CONST)
            return h == op.identity() ? l : h;
        else
            return assembler(l.op(), h.op()).assemble(op, (BooleanFormula) l, (BooleanFormula) h);
    }

    /**
     * Returns a boolean value with the same meaning as the given accumulator.
     *
     * @requires acc.components in (this.values + this.values.negation +
     *           BooleanConstant)
     * @return v: BooleanValue | [[v]] = [[acc]]
     * @ensures v in BooleanFormula - NotGate => this.values' = this.values + v,
     *          this.values' = this.values
     * @throws NullPointerException any of the arguments are null
     */
    @SuppressWarnings("unchecked" )
    BooleanValue assemble(BooleanAccumulator acc) {
        final int asize = acc.size();
        final Operator.Nary op = acc.op;
        switch (asize) {
            case 0 :
                return op.identity();
            case 1 :
                return acc.iterator().next();
            case 2 :
                final Iterator<BooleanValue> inputs = acc.iterator();
                return assemble(op, inputs.next(), inputs.next());
            default :
                @SuppressWarnings("rawtypes" )
                final int hash = op.hash((Iterator) acc.iterator());
                if (asize > cmpMax) {
                    for (Iterator<BooleanFormula> gates = opCache(op).get(hash); gates.hasNext();) {
                        BooleanFormula g = gates.next();
                        if (g.size() == asize && ((NaryGate) g).sameInputs(acc.iterator())) {
                            return g;
                        }
                    }
                } else {
                    LOOKUP: for (Iterator<BooleanFormula> gates = opCache(op).get(hash); gates.hasNext();) {
                        BooleanFormula g = gates.next();
                        if (g.size() == asize && ((NaryGate) g).sameInputs(acc.iterator())) {
                            return g;
                        } else if (g.size() < asize) {
                            scrap0.clear();
                            g.flatten(op, scrap0, cmpMax);
                            if (scrap0.size() == asize) {
                                for (BooleanValue v : acc) {
                                    if (!scrap0.contains(v))
                                        continue LOOKUP;
                                }
                                return g;
                            }
                        }
                    }
                }
                final BooleanFormula ret = new NaryGate(acc, label++, hash);
                opCache(acc.op).add(ret);
                return ret;
        }
    }

    /**
     * Given two operators, op0 and op1, returns an Assembler which contains the
     * creator method for expressions of the form v0 op v1 where op in
     * ExprOperator.Nary and v0.op = op0 and v1.op = op1.
     *
     * @requires op0 <= op1 && no (op0 + op1) & CONST
     * @requires op0 != null && op1 != null
     * @return a Assembler which contains the creator method for expressions of the
     *         form v0 op v1 where op in ExprOperator.Nary and v0.op = op0 and v1.op
     *         = op1.
     */
    private Assembler assembler(Operator op0, Operator op1) {
        return ASSEMBLERS[(op0.ordinal << 2) + op1.ordinal - ((op0.ordinal * (op0.ordinal - 1) >> 1))];
    }

    /**
     * Returns a BooleanFormula f such that [[f]] = f0 op f1. The method requires
     * that the formulas f0 and f1 be already reduced with respect to op. A new
     * formula is created and cached iff the circuit with the meaning [[f0]] op
     * [[f1]] has not already been created.
     *
     * @requires f0 and f1 have already been reduced with respect to op; i.e. f0 op
     *           f1 cannot be reduced to a constant or a simple circuit by applying
     *           absorption, idempotence, etc. laws to f0 and f1.
     * @return f : BooleanFormula | [[f]] = [[f0]] op [[f1]]
     * @ensures f !in this.values => this.values' = this.values + f, this.values' =
     *          this.values
     */
    private BooleanFormula cache(Operator.Nary op, BooleanFormula f0, BooleanFormula f1) {
        final BooleanFormula l, h;
        if (f0.label() < f1.label()) {
            l = f0;
            h = f1;
        } else {
            l = f1;
            h = f0;
        }
        final int hash = op.hash(l, h);
        if (l.op() == op || h.op() == op) {
            scrap0.clear();
            l.flatten(op, scrap0, cmpMax - 1);
            h.flatten(op, scrap0, cmpMax - scrap0.size());
            for (Iterator<BooleanFormula> gates = opCache(op).get(hash); gates.hasNext();) {
                BooleanFormula gate = gates.next();
                if (gate.size() == 2 && gate.input(0) == l && gate.input(1) == h)
                    return gate;
                else {
                    scrap1.clear();
                    gate.flatten(op, scrap1, cmpMax);
                    if (scrap0.equals(scrap1))
                        return gate;
                }
            }
        } else {
            for (Iterator<BooleanFormula> gates = opCache(op).get(hash); gates.hasNext();) {
                BooleanFormula gate = gates.next();
                if (gate.size() == 2 && gate.input(0) == l && gate.input(1) == h)
                    return gate;
            }
        }
        final BooleanFormula ret = new BinaryGate(op, label++, hash, l, h);
        opCache(op).add(ret);
        return ret;
    }

    /**
     * Wrapper for a method that generates boolean values out of existing gates,
     * using AND and OR operators.
     *
     * @author Emina Torlak
     */
    private static abstract class Assembler {

        /**
         * Returns a BooleanValue whose meaning is [[f0]] op [[f1]]. A new circuit is
         * created and cached iff [[f0]] op [[f1]] cannot be reduced to a simpler value
         * and a circuit with equivalent meaning has not already been created.
         *
         * @requires f0.op <= f1.op && f0 + f1 in CircuitFactory.this.values +
         *           CircuitFactory.this.values.negation
         * @return { v: BooleanValue | [[v]] = [[f0]] op [[f1]] }
         * @ensures (no v: CircuitFactory.this.values | [[v]] = [[f0]] op [[f1]]) =>
         *          CircuitFactory.this.values' = CircuitFactory.this.values + {v:
         *          BooleanValue | [[v]] = [[f0]] op [[f1]]} =>
         *          CircuitFactory.this.values' = CircuitFactory.this.values
         */
        abstract BooleanValue assemble(Operator.Nary op, BooleanFormula f0, BooleanFormula f1);
    }

    /**
     * Performs common simplifications on circuits of the form AND op X or OR op X,
     * where X can be any operator other than CONST (J stands for 'junction').
     */
    private final Assembler   JoX        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible. Note that these reductions
                                              * will be possible only if f0 was created after f1 (i.e. |f0.label| >
                                              * |f1.label|). (a & b) & a = a & b (a & b) & !a = F (a & b) | a = a (a | b) | a
                                              * = a | b (a | b) | !a = T (a | b) & a = a
                                              *
                                              * @requires f0.op in (AND + OR)
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op().ordinal < 2;
                                                 final int label = f1.label();
                                                 if (f0.contains(f0.op(), label, cmpMax) > 0)
                                                     return op == f0.op() ? f0 : f1;
                                                 else if (op == f0.op() && f0.contains(op, -label, cmpMax) > 0)
                                                     return op.shortCircuit();
                                                 else
                                                     return cache(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form AND op OR.
     */
    private final Assembler   AoO        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with JoX reductions.
                                              * (aj & ... & ak) & (a1 | ... | an) = (aj & ... & ak) where 1 <= j <= k <= n
                                              * (a1 & ... & an) | (aj | ... | ak) = (aj | ... | ak) where 1 <= j <= k <= n
                                              *
                                              * @requires f0.op = AND && f1.op = OR
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == AND && f1.op() == OR;
                                                 scrap0.clear();
                                                 scrap1.clear();
                                                 f0.flatten(f0.op(), scrap0, cmpMax);
                                                 f1.flatten(f1.op(), scrap1, cmpMax);
                                                 for (BooleanFormula formula : scrap1) {
                                                     if (scrap0.contains(formula))
                                                         return op == AND ? f0 : f1;
                                                 }
                                                 return (f0.label() < f1.label()) ? JoX.assemble(op, f1, f0) : JoX.assemble(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form AND op AND or OR op
     * OR.
     */
    private final Assembler   JoJ        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with the JoX
                                              * reductions. (a1 & ... & an) & (aj & ... & ak) = (a1 & ... & an) where 1 <= j
                                              * <= k <= n (a1 & ... & an) | (aj & ... & ak) = (aj & ... & ak) where 1 <= j <=
                                              * k <= n (a1 | ... | an) | (aj | ... | ak) = (a1 | ... | an) where 1 <= j <= k
                                              * <= n (a1 | ... | an) & (aj | ... | ak) = (aj | ... | ak) where 1 <= j <= k <=
                                              * n
                                              *
                                              * @requires f0.op = f1.op && (f0+f1).op in (AND + OR)
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == f1.op();
                                                 if (f0 == f1)
                                                     return f0;
                                                 final Operator fop = f0.op();
                                                 scrap0.clear();
                                                 scrap1.clear();
                                                 f0.flatten(fop, scrap0, cmpMax);
                                                 f1.flatten(fop, scrap1, cmpMax);
                                                 if (scrap0.size() < scrap1.size() && scrap1.containsAll(scrap0))
                                                     return op == fop ? f1 : f0;
                                                 else if (scrap0.size() >= scrap1.size() && scrap0.containsAll(scrap1))
                                                     return op == fop ? f0 : f1;
                                                 else if (f0.label() < f1.label())
                                                     return JoX.assemble(op, f1, f0);
                                                 else
                                                     return JoX.assemble(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form AND op ITE or OR op
     * ITE.
     */
    private final Assembler   JoI        = new Assembler() {

                                             /**
                                              * Combines JoX and IoX reductions.
                                              *
                                              * @requires f0.op in (AND + OR) && f1.op = ITE
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op().ordinal < 2 && f1.op() == ITE;
                                                 if (f0.label() < f1.label())                                                                                                                                                                                          												// f0
                                                     // created
                                                     // before
                                                     // f1
                                                     return cache(op, f1, f0);
                                                 else
                                                     return JoX.assemble(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form AND op NOT or OR op
     * NOT.
     */
    private final Assembler   JoN        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with the JoX/NoX
                                              * reductions. a & !a = F a | !a = T
                                              *
                                              * @requires f0.op in (AND + OR) && f1.op = NOT
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op().ordinal < 2 && f1.op() == NOT;
                                                 if (f0.label() == -f1.label())
                                                     return op.shortCircuit();
                                                 else if (f0.label() < StrictMath.abs(f1.label()))                                                                                                                           							// f0
                                                     // created
                                                     // before
                                                     // f1
                                                     return NoX.assemble(op, f1, f0);
                                                 else
                                                     return JoX.assemble(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form ITE op VAR.
     */
    private final Assembler   IoV        = new Assembler() {

                                             /**
                                              * Returns cache(op, f0, f1)
                                              *
                                              * @requires f0.op = ITE && f1.op = VAR
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == ITE && f1.op() == VAR;
                                                 return cache(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form ITE op NOT.
     */
    private final Assembler   IoN        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with IoX/NoX
                                              * reductions. (a ? b : c) & !(a ? b : c) = F (a ? b : c) | !(a ? b : c) = T
                                              *
                                              * @requires f0.op = ITE && f1.op = NOT
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == ITE && f1.op() == NOT;
                                                 if (f0.label() == -f1.label())
                                                     return op.shortCircuit();
                                                 else if (f0.label() < StrictMath.abs(f1.label()))                                                                                                                           							// f0
                                                     // created
                                                     // before
                                                     // f1
                                                     return NoX.assemble(op, f1, f0);
                                                 else
                                                     return cache(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form NOT op X, where X can
     * be any operator other than CONST.
     */
    private final Assembler   NoX        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible. Note that these reductions
                                              * will be possible only if f0 was created after f1 (i.e. |f0.label| >
                                              * |f1.label|). !(a | b) & a = F !(a | b) & !a = !(a | b) !(a & b) | a = T !(a &
                                              * b) | !a = !(a & b)
                                              *
                                              * @requires f0.op = NOT
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == NOT;
                                                 final int label = f1.label();
                                                 if (f0.input(0).contains(op.complement(), label, cmpMax) > 0)
                                                     return op.shortCircuit();
                                                 else if (f0.input(0).contains(op.complement(), -label, cmpMax) > 0)
                                                     return f0;
                                                 else
                                                     return cache(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form NOT op NOT.
     */
    private final Assembler   NoN        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with NoX reductions. !a
                                              * & !a = !a !a | !a = !a
                                              *
                                              * @requires f1.op + f0.op = NOT
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == NOT && f1.op() == NOT;
                                                 if (f0 == f1)
                                                     return f0;
                                                 else if (f0.label() < f1.label())                                                                                                                                                                           											// f0
                                                     // created
                                                     // after
                                                     // f1
                                                     return NoX.assemble(op, f0, f1);
                                                 else
                                                     return NoX.assemble(op, f1, f0);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form NOT op VAR.
     */
    private final Assembler   NoV        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible, along with NoX reductions. !a
                                              * & a = F !a | a = T
                                              *
                                              * @requires f1.op = NOT && f1.op = VAR
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == NOT && f1.op() == VAR;
                                                 if (f0.label() == -f1.label())
                                                     return op.shortCircuit();
                                                 else
                                                     return NoX.assemble(op, f0, f1);
                                             }
                                         };

    /**
     * Performs common simplifications on circuits of the form X op X.
     */
    private final Assembler   XoX        = new Assembler() {

                                             /**
                                              * Performs the following reductions, if possible. a & a = a a | a = a
                                              *
                                              * @requires f0.op = f1.op
                                              */
                                             @Override
                                             BooleanValue assemble(Nary op, BooleanFormula f0, BooleanFormula f1) {
                                                 assert f0.op() == f1.op();
                                                 return (f0 == f1) ? f0 : cache(op, f0, f1);
                                             }
                                         };

    /**
     * 15 Assembler entires representing all possible composition combinations of
     * non-constant vertices using the operators AND and OR. Note that there are 15
     * of them rather than 25 because of the v0.op <= v1.op requirement of the
     * {@link Assembler#assemble(ExprOperator.Nary, BooleanFormula, BooleanFormula)}
     * method.
     */
    private final Assembler[] ASSEMBLERS = {
                                            JoJ,                                                                                              /*
                                                                                                                                               * AND
                                                                                                                                               * op
                                                                                                                                               * AND
                                                                                                                                               */
                                            AoO,                                                                                              /*
                                                                                                                                               * AND
                                                                                                                                               * op
                                                                                                                                               * OR
                                                                                                                                               */
                                            JoI,                                                                                              /*
                                                                                                                                               * AND
                                                                                                                                               * op
                                                                                                                                               * ITE
                                                                                                                                               */
                                            JoN,                                                                                              /*
                                                                                                                                               * AND
                                                                                                                                               * op
                                                                                                                                               * NOT
                                                                                                                                               */
                                            JoX,                                                                                              /*
                                                                                                                                               * AND
                                                                                                                                               * op
                                                                                                                                               * VAR
                                                                                                                                               */
                                            JoJ,                                                                                              /*
                                                                                                                                               * OR
                                                                                                                                               * op
                                                                                                                                               * OR
                                                                                                                                               */
                                            JoI,                                                                                              /*
                                                                                                                                               * OR
                                                                                                                                               * op
                                                                                                                                               * ITE
                                                                                                                                               */
                                            JoN,                                                                                              /*
                                                                                                                                               * OR
                                                                                                                                               * op
                                                                                                                                               * NOT
                                                                                                                                               */
                                            JoX,                                                                                              /*
                                                                                                                                               * OR
                                                                                                                                               * op
                                                                                                                                               * VAR
                                                                                                                                               */
                                            XoX,                                                                                              /*
                                                                                                                                               * ITE
                                                                                                                                               * op
                                                                                                                                               * ITE
                                                                                                                                               */
                                            IoN,                                                                                              /*
                                                                                                                                               * ITE
                                                                                                                                               * op
                                                                                                                                               * NOT
                                                                                                                                               */
                                            IoV,                                                                                              /*
                                                                                                                                               * ITE
                                                                                                                                               * op
                                                                                                                                               * VAR
                                                                                                                                               */
                                            NoN,                                                                                              /*
                                                                                                                                               * NOT
                                                                                                                                               * op
                                                                                                                                               * NOT
                                                                                                                                               */
                                            NoV,                                                                                              /*
                                                                                                                                               * NOT
                                                                                                                                               * op
                                                                                                                                               * VAR
                                                                                                                                               */
                                            XoX                                                                                               /*
                                                                                                                                               * VAR
                                                                                                                                               * op
                                                                                                                                               * VAR
                                                                                                                                               */
    };

}
