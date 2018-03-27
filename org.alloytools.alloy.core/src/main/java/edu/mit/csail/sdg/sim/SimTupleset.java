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

package edu.mit.csail.sdg.sim;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.NoSuchElementException;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Util;

/** Immutable; represents a tupleset. */

public final class SimTupleset implements Iterable<SimTuple> {

    // if (min<max && !next) this == tuples + min..max
    // else if (min<max && next) this == tuples + { (min,min+1)...(max-1,max) }
    // else this == tuples

    public static final SimAtom       EMPTY_ATOM = SimAtom.make("∅");
    /**
     * The list of tuples. <br>
     * <b>Invariant:</b> If nonempty, it must contain only same-arity tuples. <br>
     * <b>Invariant:</b> It must not contain duplicate tuples.
     */
    private final ConstList<SimTuple> tuples;
    private final int                 min;
    private final int                 max;
    private final boolean             next;

    /**
     * Construct a tupleset with the given 4 values (Note: caller MUST make sure
     * there are no duplicates, even between (min,max) and tuples, and that all
     * tuples are of same arity!)
     */
    private SimTupleset(Collection<SimTuple> tuples, int min, int max, boolean next) {
        this.tuples = ConstList.make(tuples);
        this.min = min;
        this.max = max;
        this.next = next;
    }

    /**
     * Construct a tupleset containing the given list of tuples (Note: caller MUST
     * make sure there are no duplicates, and all tuples are of same arity!)
     */
    private SimTupleset(Collection<SimTuple> tuples) {
        this.tuples = ConstList.make(tuples);
        this.min = 0;
        this.max = 0;
        this.next = false;
    }

    /** The tupleset containing no tuples. */
    public static final SimTupleset EMPTY = new SimTupleset(new TempList<SimTuple>(0).makeConst());

    /**
     * Construct the set containing integers between min and max (inclusively).
     */
    public static SimTupleset make(int min, int max) {
        if (min > max)
            return EMPTY;
        if (min == max)
            return new SimTupleset(Util.asList(SimTuple.make(SimAtom.make(min))), 0, 0, false);
        return new SimTupleset(EMPTY.tuples, min, max, false);
    }

    /**
     * Construct the set containing (min,min+1)...(max-1,max)
     */
    public static SimTupleset makenext(int min, int max) {
        return min >= max ? EMPTY : (new SimTupleset(EMPTY.tuples, min, max, true));
    }

    /** Construct a tupleset containing the given tuple. */
    public static SimTupleset make(SimTuple tuple) {
        return new SimTupleset(Util.asList(tuple));
    }

    /** Make a tupleset containing the given atom. */
    public static SimTupleset make(String atom) {
        return make(SimTuple.make(atom));
    }

    /**
     * Make a tupleset containing a deep copy of the given list of tuples (Note:
     * caller MUST make sure there are no duplicates, and all tuples are of same
     * arity!)
     */
    public static SimTupleset make(Collection<SimTuple> tuples) {
        return tuples.size() == 0 ? EMPTY : new SimTupleset(tuples);
    }

    /**
     * If this tupleset is empty, then return 0, else return the arity of every
     * tuple in this tupleset.
     */
    public int arity() {
        return min < max ? (next ? 2 : 1) : (tuples.size() == 0 ? 0 : tuples.get(0).arity());
    }

    /** Returns the i-th tuple, or null if no such tuple. */
    private SimTuple get(long i) {
        if (i < 0)
            return null;
        long ans = (min < max) ? (max - (long) min) : 0;
        if (min < max && !next)
            ans++;
        if (i < ans) {
            SimAtom a = SimAtom.make(min + i);
            if (next)
                return SimTuple.make(a, SimAtom.make((min + i) + 1));
            else
                return SimTuple.make(a);
        }
        i = i - ans;
        if (i < tuples.size())
            return tuples.get((int) i);
        else
            return null;
    }

    /** Returns true if this is empty. */
    public boolean empty() {
        return min >= max && tuples.size() == 0;
    }

    /**
     * Returns the number of tuples in this tupleset (this answer may be truncated
     * if it cannot fit in a 32-bit integer)
     */
    public int size() {
        return (int) longsize();
    }

    /**
     * Returns the number of tuples in this tupleset (this answer will never
     * overflow)
     */
    public long longsize() {
        long ans = (min < max) ? (max - (long) min) : 0;
        if (min < max && !next)
            ans++;
        return ans + tuples.size();
    }

    /**
     * Returns true if this tupleset contains the given tuple.
     */
    public boolean has(SimTuple that) {
        if (arity() != that.arity())
            return false;
        if (min < max && !next) {
            Integer a = that.get(0).toInt(null);
            if (a != null && min <= a && a <= max)
                return true;
        }
        if (min < max && next) {
            Integer a = that.get(0).toInt(null), b = that.get(1).toInt(null);
            if (a != null && b != null && a < b && a.intValue() == b.intValue() - 1 && min <= a && b <= max)
                return true;
        }
        return tuples.contains(that);
    }

    /**
     * Returns true if this tupleset is unary and contains the given atom.
     */
    public boolean has(SimAtom that) {
        if (arity() != 1)
            return false;
        if (min < max && !next) {
            Integer a = that.toInt(null);
            if (a != null && min <= a && a <= max)
                return true;
        }
        for (int i = tuples.size() - 1; i >= 0; i--)
            if (tuples.get(i).get(0) == that)
                return true;
        return false;
    }

    /**
     * Returns an arbitrary atom from an arbitrary tuple.
     *
     * @throws ErrorAPI if this tupleset is empty
     */
    public SimAtom getAtom() throws ErrorAPI {
        if (tuples.size() > 0)
            return tuples.get(0).get(0);
        if (min >= max)
            throw new ErrorAPI("This tupleset is empty");
        return SimAtom.make(min);
    }

    /**
     * Returns an arbitrary tuple.
     *
     * @throws ErrorAPI if this tupleset is empty
     */
    public SimTuple getTuple() throws ErrorAPI {
        if (tuples.size() > 0)
            return tuples.get(0);
        if (min >= max)
            throw new ErrorAPI("This tupleset is empty");
        SimAtom a = SimAtom.make(min);
        if (next)
            return SimTuple.make(a, SimAtom.make(min + 1));
        else
            return SimTuple.make(a);
    }

    /**
     * Return the union of this and that; (if this tupleset and that tupleset does
     * not have compatible arity, then we return this tupleset as is). <br/>
     * Note: the tuples in the result will be ordered as follows: first comes the
     * tuples in "this" in original order, then the tuples that are in "that" but
     * not in "this".
     */
    public SimTupleset union(SimTupleset that) {
        if (this.empty() || this == that)
            return that;
        if (that.empty() || arity() != that.arity())
            return this;
        TempList<SimTuple> ans = null; // when null, it means we haven't found
                                      // any new tuple to add yet
        for (SimTuple x : that)
            if (!has(x)) {
                if (ans == null)
                    ans = new TempList<SimTuple>(tuples);
                ans.add(x);
            }
        return ans == null ? this : new SimTupleset(ans.makeConst(), min, max, next);
    }

    /**
     * Return the union of this and that; (if this tupleset and that tuple does not
     * have compatible arity, then we return this tupleset as is). <br/>
     * Note: if this operation is a no-op, we guarantee we'll return this
     * SimTupleset as is.
     */
    public SimTupleset union(SimTuple that) {
        if (empty())
            return make(that);
        if (arity() != that.arity() || has(that))
            return this;
        TempList<SimTuple> ans = new TempList<SimTuple>(tuples.size() + 1);
        ans.addAll(tuples).add(that);
        return new SimTupleset(ans.makeConst(), min, max, next);
    }

    // ================================================================================================================//

    /**
     * Return the tupleset where each tuple is truncated to the first N atoms; if n
     * is zero or negative, we return the emptyset; if n >= this.arity, we return
     * this as is.
     */
    public SimTupleset head(int n) {
        if (n <= 0 || empty())
            return EMPTY;
        else if (arity() <= n)
            return this;
        if (min < max) { // if we get here, than arity must be 2, and n must be
                        // 1.
            TempList<SimTuple> ans = new TempList<SimTuple>(tuples.size());
            for (SimTuple x : tuples) {
                Integer a = x.head().toInt(null);
                if (a != null && a >= min && a < max)
                    continue;
                SimTuple y = SimTuple.make(x.head());
                if (!ans.contains(y))
                    ans.add(y);
            }
            return new SimTupleset(ans.makeConst(), min, max - 1, false);
        }
        TempList<SimTuple> ans = new TempList<SimTuple>(tuples.size());
        for (SimTuple x : this) {
            SimTuple y = x.head(n);
            if (!ans.contains(y))
                ans.add(y);
        }
        return new SimTupleset(ans.makeConst());
    }

    /**
     * Return the tupleset where each tuple is truncated to the last N atoms; if n
     * is zero or negative, we return the emptyset; if n >= this.arity, we return
     * this as is.
     */
    public SimTupleset tail(int n) {
        if (n <= 0 || empty())
            return EMPTY;
        else if (arity() <= n)
            return this;
        if (min < max) { // if we get here, than arity must be 2, and n must be
                        // 1.
            TempList<SimTuple> ans = new TempList<SimTuple>(tuples.size());
            for (SimTuple x : tuples) {
                Integer a = x.tail().toInt(null);
                if (a != null && a > min && a <= max)
                    continue;
                SimTuple y = SimTuple.make(x.tail());
                if (!ans.contains(y))
                    ans.add(y);
            }
            return new SimTupleset(ans.makeConst(), min + 1, max, false);
        }
        TempList<SimTuple> ans = new TempList<SimTuple>(tuples.size());
        for (SimTuple x : this) {
            SimTuple y = x.tail(n);
            if (!ans.contains(y))
                ans.add(y);
        }
        return new SimTupleset(ans.makeConst());
    }

    /** Returns a read-only iterator over the tuples. */
    @Override
    public Iterator<SimTuple> iterator() {
        return new Iterator<SimTuple>() {

            private long n = longsize();
            private long i = 0;

            @Override
            public SimTuple next() {
                if (i >= n)
                    throw new NoSuchElementException();
                else {
                    i++;
                    return get(i - 1);
                }
            }

            @Override
            public boolean hasNext() {
                return i < n;
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * Write this SimTupleset as { (".." ".." "..") (".." ".." "..") (".." ".."
     * "..") }
     */
    void write(BufferedOutputStream out) throws IOException {
        boolean first = true;
        out.write('{');
        for (SimTuple x : this) {
            if (first)
                first = false;
            else
                out.write(' ');
            x.write(out);
        }
        out.write('}');
    }

    /**
     * Read a { (".." ".." "..") (".." ".." "..") (".." ".." "..") } tupleset.
     */
    static SimTupleset read(BufferedInputStream in) throws IOException {
        while (true) {
            int c = in.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c > 0 && c <= ' ')
                continue; // skip whitespace
            if (c == '{')
                break;
            else
                throw new IOException("Expecting start of tupleset");
        }
        LinkedHashSet<SimTuple> list = new LinkedHashSet<SimTuple>();
        while (true) {
            int c = in.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c > 0 && c <= ' ')
                continue; // skip whitespace
            if (c == '}')
                break;
            if (c != '(')
                throw new IOException("Expecting start of tuple");
            list.add(SimTuple.read(in));
            c = in.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c == '}')
                break;
            if (!(c <= ' '))
                throw new IOException("Expecting \')\' or white space after a tuple.");
        }
        return make(list);
    }

    /**
     * Returns the index position if the list of tuples contains the tuple (a,b) (or
     * return -1 if not found).
     */
    private static int find(TempList<SimTuple> tuples, SimAtom a, SimAtom b) {
        if (tuples.size() == 0 || tuples.get(0).arity() != 2)
            return -1;
        for (int i = tuples.size() - 1; i >= 0; i--) {
            SimTuple x = tuples.get(i);
            if (x.head() == a && x.tail() == b)
                return i;
        }
        return -1;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        StringBuilder sb = null;
        for (SimTuple x : this) {
            if (sb == null)
                sb = new StringBuilder("{");
            else
                sb.append(", ");
            x.toString(sb);
        }
        return sb == null ? "{}" : (sb.append("}").toString());
    }

    /**
     * Returns a hashcode consistent with the equals() method.
     */
    @Override
    public int hashCode() {
        int ans = 0;
        for (SimTuple t : this)
            ans = ans + t.hashCode();
        return ans;
    }

    /**
     * Returns true if this contains the same tuples as that.
     */
    @Override
    public boolean equals(Object that) {
        return this == that || (that instanceof SimTupleset && equals((SimTupleset) that));
    }

    /**
     * Returns true if this contains the same tuples as that.
     */
    public boolean equals(SimTupleset that) {
        // since SimTupleset must not contain duplicates, and
        // this.size()==that.size(), comparing one way is sufficient
        return this == that || (that != null && longsize() == that.longsize() && in(that));
    }

    /** Returns true if this is a subset of that. */
    public boolean in(SimTupleset that) {
        if (empty() || this == that)
            return true;
        if (longsize() > that.longsize() || arity() != that.arity())
            return false;
        for (SimTuple t : this)
            if (!that.has(t))
                return false;
        return true;
    }

    /**
     * Sum up all the integer atoms in this tupleset; (if this tupleset's arity is
     * not 1, then we return 0)
     */
    public int sum() {
        if (arity() != 1)
            return 0;
        Integer zero = 0;
        int ans = 0;
        for (SimTuple t : this)
            ans = ans + t.get(0).toInt(zero);
        return ans;
    }

    /**
     * Return the identity over this tupleset; (if this tupleset's arity is not 1,
     * then we return an emptyset) <br/>
     * Note: the result's tuple order is the same as this tupleset's tuple order.
     */
    public SimTupleset iden() {
        if (arity() != 1)
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(size());
        for (SimTuple x : this)
            ans.add(SimTuple.make(x.head(), x.head())); // since "this" has no
                                                       // duplicate tuples,
                                                       // "ans" will not have
                                                       // duplicate tuples
                                                       // either
        return new SimTupleset(ans.makeConst());
    }

    /**
     * Return the relational override of this and that; (if this tupleset and that
     * tuple does not have compatible arity, then we return this tupleset as is).
     * <br/>
     * Note: in general, the tuples may be ordered arbitrarily in the result. <br/>
     * Note: if this operation is a no-op, we guarantee we'll return this
     * SimTupleset as is.
     */
    public SimTupleset override(final SimTuple that) {
        if (arity() == 1)
            return union(that);
        if (empty())
            return SimTupleset.make(that);
        if (arity() != that.arity())
            return this;
        boolean added = false, same = false;
        TempList<SimTuple> ans = new TempList<SimTuple>(size());
        SimAtom head = that.get(0);
        for (SimTuple x : this) {
            if (x.get(0) != head) {
                ans.add(x);
                continue;
            }
            if (x.equals(that))
                same = true;
            if (!added) {
                ans.add(that);
                added = true;
            }
        }
        if (!added)
            ans.add(that);
        else if (same && longsize() == ans.size())
            return this;
        return new SimTupleset(ans.makeConst());
    }

    /**
     * Return the relational override of this and that; (if this tupleset and that
     * tupleset does not have compatible arity, then we return this tupleset as is).
     * <br/>
     * Note: in general, the tuples may be ordered arbitrarily in the result.
     */
    public SimTupleset override(SimTupleset that) throws ErrorAPI {
        if (arity() == 1)
            return union(that);
        if (this.empty() || this == that)
            return that;
        if (that.empty() || this.arity() != that.arity())
            return this;
        if (that.longsize() == 1)
            return override(that.getTuple()); // very common case, so let's
                                             // optimize it
        TempList<SimTuple> ans = new TempList<SimTuple>(size());
        for (SimTuple x : this)
            if (!that.has(x))
                ans.add(x);
        ans.addAll(that);
        return new SimTupleset(ans.makeConst());
    }

    /**
     * Return this minus that; (if this tupleset and that tupleset does not have
     * compatible arity, then we return this tupleset as is). <br/>
     * Note: The resulting tuples will keep their original order.
     */
    public SimTupleset difference(SimTupleset that) {
        if (this.empty() || this == that)
            return EMPTY;
        if (that.empty() || arity() != that.arity())
            return this;
        TempList<SimTuple> ans = new TempList<SimTuple>(size() - 1);
        for (SimTuple x : this)
            if (!that.has(x))
                ans.add(x);
        return ans.size() == longsize() ? this : (ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst()));
    }

    /**
     * Return this minus that; (if this tupleset and that tuple does not have
     * compatible arity, then we return this tupleset as is). <br/>
     * Note: The resulting tuples will keep their original order. <br/>
     * Note: if this operation is a no-op, we guarantee we'll return this
     * SimTupleset as is.
     */
    public SimTupleset difference(SimTuple that) {
        if (empty() || arity() != that.arity())
            return this;
        TempList<SimTuple> ans = new TempList<SimTuple>(size() - 1);
        for (SimTuple x : this) {
            if (that == null || !x.equals(that))
                ans.add(x);
            else
                that = null;
        }
        return that != null ? this : (ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst()));
    }

    /**
     * Return this minus any tuple that contains the given atom. <br/>
     * Note: The resulting tuples will keep their original order.
     */
    public SimTupleset removeAll(SimAtom that) {
        if (empty())
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(size() - 1);
        again: for (SimTuple x : this) {
            for (int i = x.arity() - 1; i >= 0; i--)
                if (x.get(i) == that)
                    continue again;
            ans.add(x);
        }
        return ans.size() == longsize() ? this : (ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst()));
    }

    /**
     * Return the transpose of this tupleset; (if this tupleset's arity is not 2,
     * we'll return an empty set instead)
     */
    public SimTupleset transpose() {
        if (empty() || arity() != 2)
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(size());
        for (SimTuple x : this)
            ans.add(SimTuple.make(x.tail(), x.head())); // since "this" has no
                                                       // duplicate tuples,
                                                       // "ans" will not have
                                                       // duplicate tuples
                                                       // either
        return new SimTupleset(ans.makeConst());
    }

    /** Return the cartesian product of this and that. */
    public SimTupleset product(SimTupleset that) {
        if (empty() || that.empty())
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(size() * that.size());
        for (SimTuple a : this)
            for (SimTuple b : that) {
                ans.add(a.product(b)); // We don't have to check for duplicates,
                                      // because we assume every tuple in
                                      // "this" has same arity, and every
                                      // tuple in "that" has same arity
            }
        return new SimTupleset(ans.makeConst());
    }

    /**
     * Return the relational join between this and that (throws ErrorType if
     * this.arity==1 and that.arity==1)
     */
    public SimTupleset join(SimTupleset that) throws ErrorType {
        if (empty() || that.empty())
            return EMPTY;
        if (arity() == 1 && that.arity() == 1)
            throw new ErrorType("Cannot join two unary relations.");
        TempList<SimTuple> ans = new TempList<SimTuple>();
        for (SimTuple a : this)
            for (SimTuple b : that)
                if (a.tail() == b.head()) {
                    SimTuple c = a.join(b);
                    if (!ans.contains(c))
                        ans.add(c);
                }
        return ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst());
    }

    /** Return the intersection of this and that. */
    public SimTupleset intersect(SimTupleset that) {
        if (this == that)
            return this;
        else if (empty() || that.empty())
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(size() < that.size() ? size() : that.size());
        for (SimTuple x : that)
            if (has(x))
                ans.add(x);
        if (ans.size() == 0)
            return EMPTY;
        if (ans.size() == this.longsize())
            return this;
        if (ans.size() == that.longsize())
            return that;
        else
            return new SimTupleset(ans.makeConst());
    }

    /**
     * Return true if the intersection of this and that is nonempty.
     */
    public boolean intersects(SimTupleset that) {
        if (empty())
            return false;
        if (this == that)
            return true;
        for (SimTuple x : that)
            if (has(x))
                return true;
        return false;
    }

    /**
     * Returns this<:that (NOTE: if this.arity!=1, then we return the empty set)
     */
    public SimTupleset domain(SimTupleset that) {
        if (arity() != 1 || that.empty())
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(that.size());
        for (SimTuple x : that)
            if (has(x.head()))
                ans.add(x);
        return ans.size() == that.longsize() ? that : (ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst()));
    }

    /**
     * Returns this:>that (NOTE: if that.arity!=1, then we return the empty set)
     */
    public SimTupleset range(SimTupleset that) {
        if (that.arity() != 1 || this.empty())
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>(this.size());
        for (SimTuple x : this)
            if (that.has(x.head()))
                ans.add(x);
        return ans.size() == this.longsize() ? this : (ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst()));
    }

    /**
     * Returns the closure of this tupleset (NOTE: if this.arity!=2, we will return
     * an empty set)
     */
    public SimTupleset closure() {
        if (arity() != 2)
            return EMPTY;
        TempList<SimTuple> ar = new TempList<SimTuple>(size());
        ar.addAll(this);
        while (true) {
            int n = ar.size();
            for (int i = 0; i < n; i++) {
                SimTuple left = ar.get(i);
                if (left.head() == left.tail())
                    continue; // whatever "right" is, "left.right" won't add any
                             // new tuple to the final answer
                for (int j = 0; j < n; j++)
                    if (i != j) { // whatever "left" is, "left.left" won't add
                                 // any new tuple to the final answer
                        SimTuple right = ar.get(j);
                        if (right.head() == right.tail())
                            continue; // whatever "left" is, "left.right" won't
                                     // add any new tuple to the final answer
                        if (left.tail() == right.head() && find(ar, left.head(), right.tail()) < 0)
                            ar.add(SimTuple.make(left.head(), right.tail()));
                    }
            }
            if (n == ar.size())
                return ar.size() == longsize() ? this : new SimTupleset(ar.makeConst()); // if
                                                                                        // we
                                                                                        // went
                                                                                        // through
                                                                                        // the
                                                                                        // loop
                                                                                        // without
                                                                                        // making
                                                                                        // any
                                                                                        // change,
                                                                                        // we're
                                                                                        // done
        }
    }

    /**
     * Return the set of tuples which begins with the given tuple (where we remove
     * the "matching leading part")
     */
    public SimTupleset beginWith(SimTuple x) {
        int shift = arity() - x.arity();
        if (shift <= 0)
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>();
        again: for (SimTuple r : this) {
            for (int i = 0; i < x.arity(); i++)
                if (r.get(i) != x.get(i))
                    continue again;
            ans.add(r.tail(shift));
        }
        return ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst());
    }

    /**
     * Return the set of tuples which ends with the given tuple (where we remove the
     * "matching trailing part")
     */
    public SimTupleset endWith(SimTuple x) {
        int shift = arity() - x.arity();
        if (shift <= 0)
            return EMPTY;
        TempList<SimTuple> ans = new TempList<SimTuple>();
        again: for (SimTuple r : this) {
            for (int i = 0; i < x.arity(); i++)
                if (r.get(i + shift) != x.get(i))
                    continue again;
            ans.add(r.head(shift));
        }
        return ans.size() == 0 ? EMPTY : new SimTupleset(ans.makeConst());
    }

    /**
     * Returns a modifiable copy of the list of all i-th atom from all tuples in
     * some arbitrary order (0 is first atom, 1 is second atom...)
     *
     * @throws ErrorAPI if this tupleset contains at least one tuple whose length is
     *             less than or equal to i
     */
    public List<SimAtom> getAllAtoms(int column) throws ErrorAPI {
        if (empty())
            return new ArrayList<SimAtom>(0);
        if (column < 0 || column >= arity())
            throw new ErrorAPI("This tupleset does not have an \"" + column + "th\" column.");
        IdentityHashMap<SimAtom,Boolean> ans = new IdentityHashMap<SimAtom,Boolean>();
        for (SimTuple x : this)
            ans.put(x.get(column), Boolean.TRUE);
        return new ArrayList<SimAtom>(ans.keySet());
    }

    /**
     * Return true if this is a total ordering over "elem", with "first" being the
     * first element of the total order.
     */
    public boolean totalOrder(SimTupleset elem, SimTupleset first) throws ErrorAPI {
        if (elem.empty())
            return false;
        if (elem.longsize() == 1)
            return elem.arity() == 1 && first.equals(elem) && empty();
        if (first.longsize() != 1 || first.arity() != 1 || elem.arity() != 1 || arity() != 2 || longsize() != elem.longsize() - 1)
            return false;
        SimAtom e = first.getAtom();
        List<SimAtom> elems = elem.getAllAtoms(0);
        if (longsize() > Integer.MAX_VALUE)
            throw new OutOfMemoryError();
        List<SimTuple> next = new ArrayList<SimTuple>(size());
        for (SimTuple x : this)
            next.add(x);
        while (true) {
            // "e" must be in elems; remove it from elems
            for (int n = elems.size(), i = 0;; i++)
                if (i >= n)
                    return false;
                else if (elems.get(i) == e) {
                    elems.set(i, elems.get(n - 1));
                    elems.remove(n - 1);
                    break;
                }
            // if "e" was the last element, then "next" must be empty as well
            if (elems.size() == 0)
                return next.size() == 0;
            // remove (e,e') from next and let e' be the new e
            // (if there was a cycle, we would eventually detect that since the
            // repeated element would no longer be in "elems")
            for (int n = next.size(), i = 0;; i++)
                if (i >= n)
                    return false;
                else if (e == next.get(i).head()) {
                    e = next.get(i).tail();
                    next.set(i, next.get(n - 1));
                    next.remove(n - 1);
                    break;
                }
        }
    }

    /**
     * Return an iterator over all subset x of this where x.size<=1
     */
    public Iterator<SimTupleset> loneOf() {
        return new Iterator<SimTupleset>() {

            private long i = (-1); // -1 if we haven't started yet; otherwise it
                                  // is the next element to return

            @Override
            public SimTupleset next() {
                if (i < 0) {
                    i++;
                    return EMPTY;
                } else if (i >= longsize())
                    throw new NoSuchElementException();
                SimTupleset ans = make(get(i));
                i++;
                return ans;
            }

            @Override
            public boolean hasNext() {
                return i < longsize();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * Return an iterator over all subset x of this where x.size==1
     */
    public Iterator<SimTupleset> oneOf() {
        Iterator<SimTupleset> ans = loneOf();
        ans.next(); // here, we depend on our knowledge that loneOf() will
                   // always return the emptyset first, so we can skip it up
                   // front
        return ans;
    }

    /** Return an iterator over all subset x of this */
    public Iterator<SimTupleset> setOf() {
        if (longsize() > Integer.MAX_VALUE)
            throw new OutOfMemoryError();
        return new Iterator<SimTupleset>() {

            private boolean in[] = new boolean[size()]; // indicates whether
                                                       // each tuple should
                                                       // appear in the
                                                       // upcoming tupleset; if
                                                       // null, it means no
                                                       // more results

            @Override
            public SimTupleset next() {
                if (in == null)
                    throw new NoSuchElementException();
                TempList<SimTuple> ans = new TempList<SimTuple>();
                for (int i = 0; i < in.length; i++)
                    if (in[i])
                        ans.add(get(i));
                for (int i = 0;; i++)
                    if (i == in.length) {
                        in = null;
                        break;
                    } else if (!in[i]) {
                        in[i] = true;
                        break;
                    } else {
                        in[i] = false;
                    }
                return new SimTupleset(ans.makeConst());
            }

            @Override
            public boolean hasNext() {
                return in != null;
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * Return an iterator over all subset x of this where x.size>=1
     */
    public Iterator<SimTupleset> someOf() {
        Iterator<SimTupleset> ans = setOf();
        ans.next(); // here, we depend on our knowledge that setOf() will always
                   // return the emptyset first, so we can skip it up front
        return ans;
    }
}
