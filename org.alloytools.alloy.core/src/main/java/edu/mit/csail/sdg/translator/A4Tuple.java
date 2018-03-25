/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Type;
import kodkod.instance.Tuple;

/**
 * Immutable; represents a single Alloy tuple; comparison is by identity rather
 * than by value.
 */

public final class A4Tuple {

    /** The Kodkod tuple. */
    private final Tuple      tuple;

    /** The A4Solution that this came from. */
    private final A4Solution sol;

    /**
     * Construct a Tuple from the kodkod Tuple, while renaming each atom using the
     * atom2name map in sol. <br>
     * NOTE: caller must ensure the Kodkod tuple is not modified, since we expect
     * the resulting A4Tuple to be constant.
     */
    A4Tuple(Tuple tuple, A4Solution sol) {
        this.tuple = tuple;
        this.sol = sol;
    }

    /** Returns the arity. */
    public int arity() {
        return tuple.arity();
    }

    /**
     * Returns the type constructed by taking the product for each sig in this
     * tuple.
     */
    public Type type() {
        Type ans = null;
        for (int i = 0; i < tuple.arity(); i++)
            if (ans == null)
                ans = sig(0).type();
            else
                ans = ans.product(sig(i).type());
        return ans;
    }

    /** Returns the i-th atom in this Tuple. */
    public String atom(int i) {
        return sol.atom2name(tuple.atom(i));
    }

    /**
     * Return the most-specific-sig for the i-th atom in this Tuple.
     */
    public PrimSig sig(int i) {
        return sol.atom2sig(tuple.atom(i));
    }

    /** Prints a human-readable description of this Tuple. */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < tuple.arity(); i++) {
            if (i > 0)
                sb.append("->");
            sb.append(atom(i));
        }
        return sb.toString();
    }
}
