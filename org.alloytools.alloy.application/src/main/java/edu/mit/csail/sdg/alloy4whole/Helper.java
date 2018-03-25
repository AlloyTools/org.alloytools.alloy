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

package edu.mit.csail.sdg.alloy4whole;

import java.util.HashMap;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;

/**
 * This class contains convenient methods for people using Alloy4 API. These
 * methods are provided for your convenience, and any discovered bug will be
 * fixed, but these methods are not part of the official Alloy4 API and
 * individual methods may be removed in the future if necessary.
 */

public final class Helper {

    /**
     * Given an A4Solution, return a map that maps every atom to its most specific
     * signature.
     * <p>
     * For example, suppose we have "sig Animal { }" and "sig Dog, Cat extends
     * Animal { }". Suppose the solution says Animal={A$1, A$2, A$3, A$4} and
     * Dog={A$1} and Cat={A$2, A$3}. This method will return a map that maps A$1 to
     * Dog, A$2 to Cat, A$3 to Cat, and A$4 to Animal. (A$1 is both an Animal and a
     * Dog, but Dog is a subtype of Animal, so Dog is A$1's most specific signature)
     */
    public static Map<String,PrimSig> atom2sig(A4Solution solution) throws Err {
        Map<String,PrimSig> map = new HashMap<String,PrimSig>();
        for (Sig s : solution.getAllReachableSigs())
            if (s instanceof PrimSig)
                for (A4Tuple t : solution.eval(s)) {
                    // We skip over SubsetSig and only care about PrimSig
                    String atom = t.atom(0);
                    PrimSig old = map.get(atom);
                    if (old == null || ((PrimSig) s).isSameOrDescendentOf(old)) {
                        map.put(atom, (PrimSig) s);
                    }
                }
        return map;
    }

    /**
     * Constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private Helper() {}
}
