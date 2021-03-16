/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.tools;

import java.math.BigInteger;

import org.sat4j.annotations.Feature;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;

/**
 * Utility class to easily feed a SAT solver using logical gates.
 * 
 * @author leberre
 * 
 */
@Feature("solver")
public class GateTranslator extends SolverDecorator<ISolver> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public GateTranslator(ISolver solver) {
        super(solver);
    }

    /**
     * translate <code>y &lt;=&gt; FALSE</code> into a clause.
     * 
     * @param y
     *            a variable to falsify
     * @throws ContradictionException
     *             iff a trivial inconsistency is found.
     * @since 2.1
     */
    public IConstr gateFalse(int y) throws ContradictionException {
        IVecInt clause = new VecInt(2);
        clause.push(-y);
        return processClause(clause);
    }

    /**
     * translate <code>y &lt;=&gt; TRUE</code> into a clause.
     * 
     * @param y
     *            a variable to verify
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr gateTrue(int y) throws ContradictionException {
        IVecInt clause = new VecInt(2);
        clause.push(y);
        return processClause(clause);
    }

    /**
     * translate <code>y &lt;=&gt; if x1 then x2 else x3</code> into clauses.
     * 
     * @param y
     * @param x1
     *            the selector variable
     * @param x2
     * @param x3
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] ite(int y, int x1, int x2, int x3)
            throws ContradictionException {
        IConstr[] constrs = new IConstr[6];
        IVecInt clause = new VecInt(5);
        // y &lt;=&gt; (x1 -> x2) and (not x1 -> x3)
        // y -> (x1 -> x2) and (not x1 -> x3)
        clause.push(-y).push(-x1).push(x2);
        constrs[0] = processClause(clause);
        clause.clear();
        clause.push(-y).push(x1).push(x3);
        constrs[1] = processClause(clause);
        // y <- (x1 -> x2) and (not x1 -> x3)
        // not(x1 -> x2) or not(not x1 -> x3) or y
        // x1 and not x2 or not x1 and not x3 or y
        // (x1 and not x2) or ((not x1 or y) and (not x3 or y))
        // (x1 or not x1 or y) and (not x2 or not x1 or y) and (x1 or not x3 or
        // y) and (not x2 or not x3 or y)
        // not x1 or not x2 or y and x1 or not x3 or y and not x2 or not x3 or y
        clause.clear();
        clause.push(-x1).push(-x2).push(y);
        constrs[2] = processClause(clause);
        clause.clear();
        clause.push(x1).push(-x3).push(y);
        constrs[3] = processClause(clause);
        clause.clear();
        clause.push(-x2).push(-x3).push(y);
        constrs[4] = processClause(clause);
        // taken from Niklas Een et al SAT 2007 paper
        // Adding the following redundant clause will improve unit propagation
        // y -> x2 or x3
        clause.clear();
        clause.push(-y).push(x2).push(x3);
        constrs[5] = processClause(clause);
        return constrs;
    }

    /**
     * translate <code>y &lt;=&gt; (x1 =&gt; x2)</code>
     * 
     * @param y
     * @param x1
     *            the selector variable
     * @param x2
     * @return
     * @throws ContradictionException
     * @since 2.3.6
     */
    public IConstr[] it(int y, int x1, int x2) throws ContradictionException {
        IConstr[] constrs = new IConstr[3];
        IVecInt clause = new VecInt(5);
        // y &lt;=&gt; (x1 -> x2)
        // y -> (x1 -> x2)
        clause.push(-y).push(-x1).push(x2);
        constrs[0] = processClause(clause);
        clause.clear();
        // y <- (x1 -> x2)
        // not(x1 -> x2) or y
        // x1 and not x2 or y
        // (x1 or y) and (not x2 or y)
        clause.push(x1).push(y);
        constrs[1] = processClause(clause);
        clause.clear();
        clause.push(-x2).push(y);
        constrs[2] = processClause(clause);

        return constrs;
    }

    /**
     * Translate <code>y &lt;=&gt; x1 /\ x2 /\ ... /\ xn</code> into clauses.
     * 
     * @param y
     * @param literals
     *            the x1 ... xn literals.
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] and(int y, IVecInt literals)
            throws ContradictionException {
        // y &lt;=&gt; AND x1 ... xn
        IConstr[] constrs = new IConstr[literals.size() + 1];
        // y <= x1 .. xn
        IVecInt clause = new VecInt(literals.size() + 2);
        clause.push(y);
        for (int i = 0; i < literals.size(); i++) {
            clause.push(-literals.get(i));
        }
        constrs[0] = processClause(clause);
        clause.clear();
        for (int i = 0; i < literals.size(); i++) {
            // y => xi
            clause.clear();
            clause.push(-y);
            clause.push(literals.get(i));
            constrs[i + 1] = processClause(clause);
        }
        return constrs;
    }

    /**
     * Translate <code>y &lt;=&gt; x1 /\ x2</code>
     * 
     * @param y
     * @param x1
     * @param x2
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] and(int y, int x1, int x2) throws ContradictionException {
        IVecInt clause = new VecInt(4);
        IConstr[] constrs = new IConstr[3];
        clause.push(-y);
        clause.push(x1);
        constrs[0] = addClause(clause);
        clause.clear();
        clause.push(-y);
        clause.push(x2);
        constrs[1] = addClause(clause);
        clause.clear();
        clause.push(y);
        clause.push(-x1);
        clause.push(-x2);
        constrs[2] = addClause(clause);
        return constrs;
    }

    /**
     * translate <code>y &lt;=&gt; x1 \/ x2 \/ ... \/ xn</code> into clauses.
     * 
     * @param y
     * @param literals
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] or(int y, IVecInt literals) throws ContradictionException {
        // y &lt;=&gt; OR x1 x2 ...xn
        // y => x1 x2 ... xn
        IConstr[] constrs = new IConstr[literals.size() + 1];
        IVecInt clause = new VecInt(literals.size() + 2);
        literals.copyTo(clause);
        clause.push(-y);
        constrs[0] = processClause(clause);
        clause.clear();
        for (int i = 0; i < literals.size(); i++) {
            // xi => y
            clause.clear();
            clause.push(y);
            clause.push(-literals.get(i));
            constrs[i + 1] = processClause(clause);
        }
        return constrs;
    }

    /**
     * translate <code>y &lt;= x1 \/ x2 \/ ... \/ xn</code> into clauses.
     * 
     * @param y
     * @param literals
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] halfOr(int y, IVecInt literals)
            throws ContradictionException {
        IConstr[] constrs = new IConstr[literals.size()];
        IVecInt clause = new VecInt(literals.size() + 2);
        for (int i = 0; i < literals.size(); i++) {
            // xi => y
            clause.clear();
            clause.push(y);
            clause.push(-literals.get(i));
            constrs[i] = processClause(clause);
        }
        return constrs;
    }

    private IConstr processClause(IVecInt clause)
            throws ContradictionException {
        return addClause(clause);
    }

    /**
     * Translate <code>y &lt;=&gt; not x</code> into clauses.
     * 
     * @param y
     * @param x
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] not(int y, int x) throws ContradictionException {
        IConstr[] constrs = new IConstr[2];
        IVecInt clause = new VecInt(3);
        // y &lt;=&gt; not x
        // y => not x = not y or not x
        clause.push(-y).push(-x);
        constrs[0] = processClause(clause);
        // y <= not x = y or x
        clause.clear();
        clause.push(y).push(x);
        constrs[1] = processClause(clause);
        return constrs;
    }

    /**
     * translate <code>y &lt;=&gt; x1 xor x2 xor ... xor xn</code> into clauses.
     * 
     * @param y
     * @param literals
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] xor(int y, IVecInt literals)
            throws ContradictionException {
        literals.push(-y);
        int[] f = new int[literals.size()];
        literals.copyTo(f);
        IVec<IConstr> vconstrs = new Vec<IConstr>();
        xor2Clause(f, 0, false, vconstrs);
        IConstr[] constrs = new IConstr[vconstrs.size()];
        vconstrs.copyTo(constrs);
        return constrs;
    }

    /**
     * translate <code>y &lt;=&gt; x1 xor x2 xor ... xor xn</code> into a native
     * xor constraint.
     * 
     * @param y
     * @param literals
     * @return a native xor constraint
     * @since 2.3.6
     * 
     */
    public IConstr nativeXor(int y, IVecInt literals) {
        literals.push(-y);
        return addParity(literals, false);
    }

    /**
     * translate
     * <code>y &lt;=&gt; (x1 &lt;=&gt; x2 &lt;=&gt; ... &lt;=&gt; xn)</code>
     * into clauses.
     * 
     * @param y
     * @param literals
     * @throws ContradictionException
     * @since 2.1
     */
    public IConstr[] iff(int y, IVecInt literals)
            throws ContradictionException {
        literals.push(y);
        int[] f = new int[literals.size()];
        literals.copyTo(f);
        IVec<IConstr> vconstrs = new Vec<IConstr>();
        iff2Clause(f, 0, false, vconstrs);
        IConstr[] constrs = new IConstr[vconstrs.size()];
        vconstrs.copyTo(constrs);
        return constrs;
    }

    /**
     * @since 2.2
     */
    public void xor(int x, int a, int b) throws ContradictionException {
        IVecInt clause = new VecInt(3);
        clause.push(-a).push(b).push(x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(-b).push(x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(-b).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(b).push(-x);
        processClause(clause);
        clause.clear();
    }

    private void xor2Clause(int[] f, int prefix, boolean negation,
            IVec<IConstr> constrs) throws ContradictionException {
        if (prefix == f.length - 1) {
            IVecInt clause = new VecInt(f.length + 1);
            for (int i = 0; i < f.length - 1; ++i) {
                clause.push(f[i]);
            }
            clause.push(f[f.length - 1] * (negation ? -1 : 1));
            constrs.push(processClause(clause));
            return;
        }

        if (negation) {
            f[prefix] = -f[prefix];
            xor2Clause(f, prefix + 1, false, constrs);
            f[prefix] = -f[prefix];

            xor2Clause(f, prefix + 1, true, constrs);
        } else {
            xor2Clause(f, prefix + 1, false, constrs);

            f[prefix] = -f[prefix];
            xor2Clause(f, prefix + 1, true, constrs);
            f[prefix] = -f[prefix];
        }
    }

    private void iff2Clause(int[] f, int prefix, boolean negation,
            IVec<IConstr> constrs) throws ContradictionException {
        if (prefix == f.length - 1) {
            IVecInt clause = new VecInt(f.length + 1);
            for (int i = 0; i < f.length - 1; ++i) {
                clause.push(f[i]);
            }
            clause.push(f[f.length - 1] * (negation ? -1 : 1));
            processClause(clause);
            return;
        }

        if (negation) {
            iff2Clause(f, prefix + 1, false, constrs);
            f[prefix] = -f[prefix];
            iff2Clause(f, prefix + 1, true, constrs);
            f[prefix] = -f[prefix];
        } else {
            f[prefix] = -f[prefix];
            iff2Clause(f, prefix + 1, false, constrs);
            f[prefix] = -f[prefix];
            iff2Clause(f, prefix + 1, true, constrs);
        }
    }

    // From Een and Sorensson JSAT 2006 paper

    /**
     * @since 2.2
     */
    public void fullAdderSum(int x, int a, int b, int c)
            throws ContradictionException {
        IVecInt clause = new VecInt(4);
        // -a /\ -b /\ -c -> -x
        clause.push(a).push(b).push(c).push(-x);
        processClause(clause);
        clause.clear();
        // -a /\ b /\ c -> -x
        clause.push(a).push(-b).push(-c).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(b).push(-c).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(-b).push(c).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(-b).push(-c).push(x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(b).push(c).push(x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(-b).push(c).push(x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(b).push(-c).push(x);
        processClause(clause);
        clause.clear();
    }

    /**
     * @since 2.2
     */
    public void fullAdderCarry(int x, int a, int b, int c)
            throws ContradictionException {
        IVecInt clause = new VecInt(3);
        clause.push(-b).push(-c).push(x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(-c).push(x);
        processClause(clause);
        clause.clear();
        clause.push(-a).push(-b).push(x);
        processClause(clause);
        clause.clear();
        clause.push(b).push(c).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(c).push(-x);
        processClause(clause);
        clause.clear();
        clause.push(a).push(b).push(-x);
        processClause(clause);
        clause.clear();
    }

    /**
     * @since 2.2
     */
    public void additionalFullAdderConstraints(int xcarry, int xsum, int a,
            int b, int c) throws ContradictionException {
        IVecInt clause = new VecInt(3);
        clause.push(-xcarry).push(-xsum).push(a);
        processClause(clause);
        clause.push(-xcarry).push(-xsum).push(b);
        processClause(clause);
        clause.push(-xcarry).push(-xsum).push(c);
        processClause(clause);
        clause.push(xcarry).push(xsum).push(-a);
        processClause(clause);
        clause.push(xcarry).push(xsum).push(-b);
        processClause(clause);
        clause.push(xcarry).push(xsum).push(-c);
        processClause(clause);
    }

    /**
     * @since 2.2
     */
    public void halfAdderSum(int x, int a, int b)
            throws ContradictionException {
        xor(x, a, b);
    }

    /**
     * @since 2.2
     */
    public void halfAdderCarry(int x, int a, int b)
            throws ContradictionException {
        and(x, a, b);
    }

    /**
     * Translate an optimization function into constraints and provides the
     * binary literals in results. Works only when the value of the objective
     * function is positive.
     * 
     * @since 2.2
     */
    public void optimisationFunction(IVecInt literals, IVec<BigInteger> coefs,
            IVecInt result) throws ContradictionException {
        IVec<IVecInt> buckets = new Vec<IVecInt>();
        IVecInt bucket;
        // filling the buckets
        for (int i = 0; i < literals.size(); i++) {
            int p = literals.get(i);
            BigInteger a = coefs.get(i);
            for (int j = 0; j < a.bitLength(); j++) {
                bucket = createIfNull(buckets, j);
                if (a.testBit(j)) {
                    bucket.push(p);
                }
            }
        }
        // creating the adder
        int x, y, z;
        int sum, carry;
        for (int i = 0; i < buckets.size(); i++) {
            bucket = buckets.get(i);
            while (bucket.size() >= 3) {
                x = bucket.get(0);
                y = bucket.get(1);
                z = bucket.get(2);
                bucket.remove(x);
                bucket.remove(y);
                bucket.remove(z);
                sum = nextFreeVarId(true);
                carry = nextFreeVarId(true);
                fullAdderSum(sum, x, y, z);
                fullAdderCarry(carry, x, y, z);
                additionalFullAdderConstraints(carry, sum, x, y, z);
                bucket.push(sum);
                createIfNull(buckets, i + 1).push(carry);
            }
            while (bucket.size() == 2) {
                x = bucket.get(0);
                y = bucket.get(1);
                bucket.remove(x);
                bucket.remove(y);
                sum = nextFreeVarId(true);
                carry = nextFreeVarId(true);
                halfAdderSum(sum, x, y);
                halfAdderCarry(carry, x, y);
                bucket.push(sum);
                createIfNull(buckets, i + 1).push(carry);
            }
            assert bucket.size() == 1;
            result.push(bucket.last());
            bucket.pop();
            assert bucket.isEmpty();
        }
    }

    /**
     * Create a new bucket if it does not exists. Works only because the buckets
     * are explored in increasing order.
     * 
     * @param buckets
     * @param i
     * @return
     */
    private IVecInt createIfNull(IVec<IVecInt> buckets, int i) {
        IVecInt bucket = buckets.get(i);
        if (bucket == null) {
            bucket = new VecInt();
            buckets.push(bucket);
            assert buckets.get(i) == bucket;
        }
        return bucket;

    }
}
