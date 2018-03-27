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

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.ast.Sig.NONE;
import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

/**
 * Immutable; represents the type of an expression.
 * <p>
 * <b>Invariant:</b> all x:entries | x.arity()>0
 * <p>
 * Note: except for "toString()" and "fold()", the return value of every method
 * is always valid for all time; for example, given types A and B, and you call
 * C=A.intersect(B), then the result C will always be the intersection of A and
 * B even if the caller later constructs more sigs or subsigs or subsetsigs...
 */

public final class Type implements Iterable<Type.ProductType>, Clause {

    // [AM]
    // /** This configuration option is true if we want to automatically cast
    // from int to Int when necessary. */
    // public static final boolean INT2SIGINT=true;
    //
    // /** This configuration option is true if we want to automatically cast
    // from Int to int when necessary. */
    // public static final boolean SIGINT2INT=true;

    /**
     * Immutable; represents a list of PrimSig objects.
     * <p>
     * <b>Invariant:</b> "one of the sig in the list is NONE" iff "every sig in the
     * list is NONE".
     * <p>
     * Note: the return value of every method is always valid for all time; for
     * example, given ProductType A and B, and you call C=A.intersect(B), then the
     * result C will always be the intersection of A and B even if the caller later
     * constructs more sigs or subsigs or subsetsigs...
     */
    public static final class ProductType {

        /** The array of PrimSig objects. */
        private final PrimSig[]          types;

        /** The ProductType with arity==0 */
        private static final ProductType zero = new ProductType(new PrimSig[0]);

        /**
         * Constructs a new ProductType object consisting of the given array of PrimSig
         * objects.
         * <p>
         * Precondition: "one of the sig in the list is NONE" iff "every sig in the list
         * is NONE"
         * <p>
         * Note: it will use the array as-is, so the caller should give up its reference
         * to the array.
         * <p>
         * Note: this constructor promises it won't call any method or read anything
         * from any of the sig(s).
         */
        private ProductType(PrimSig[] array) {
            types = array;
        }

        /**
         * Constructs a new ProductType made of exactly 1 PrimSig;
         * <p>
         * Note: this constructor promises it won't call any method or read anything
         * from the sig.
         */
        private ProductType(PrimSig sig) {
            types = new PrimSig[] {
                                   sig
            };
        }

        /**
         * Constructs a new ProductType made of exactly n references to the same PrimSig
         * object.
         * <p>
         * Note: this constructor promises it won't call any method or read anything
         * from the sig.
         */
        private ProductType(int n, PrimSig sig) {
            types = new PrimSig[n];
            for (int i = 0; i < n; i++) {
                types[i] = sig;
            }
        }

        /** Returns a hash code consistent with equals() */
        @Override
        public int hashCode() {
            return types.length == 0 ? 0 : (types[0].hashCode());
        }

        /**
         * Returns true if this.arity==that.arity and this.types[i]==that.types[i] for
         * each i
         */
        @Override
        public boolean equals(Object that) {
            if (this == that)
                return true;
            if (!(that instanceof ProductType))
                return false;
            ProductType x = (ProductType) that;
            if (types.length != x.types.length)
                return false;
            for (int i = types.length - 1; i >= 0; i--)
                if (types[i] != x.types[i])
                    return false;
            return true;
        }

        /**
         * Returns true if (this[i] is equal or subtype of that[i]) for every i.
         * <p>
         * Precondition: this.arity == that.arity
         */
        private boolean isSubtypeOf(ProductType that) {
            if (this == that)
                return true;
            for (int i = types.length - 1; i >= 0; i--)
                if (!types[i].isSameOrDescendentOf(that.types[i]))
                    return false;
            return true;
        }

        /**
         * Returns true if (this[i] is equal or subtype of that[i]) for every i.
         * <p>
         * Precondition: this.arity == that.arity
         */
        private boolean isSubtypeOf(List<PrimSig> that) {
            for (int i = types.length - 1; i >= 0; i--)
                if (!types[i].isSameOrDescendentOf(that.get(i)))
                    return false;
            return true;
        }

        /** Returns the arity of this ProductType object. */
        public int arity() {
            return types.length;
        }

        /**
         * Returns a specific PrimSig in this ProductType
         *
         * @throws ArrayIndexOutOfBoundsException if (i < 0) or (i >= arity)
         */
        public PrimSig get(int i) {
            return types[i];
        }

        /** Returns true if this.arity==0 or this==NONE->..->NONE */
        public boolean isEmpty() {
            return types.length == 0 || types[0] == NONE;
        }

        /**
         * Returns the tranpose of this
         * <p>
         * Precondition: this.arity()==2
         */
        private ProductType transpose() {
            if (types[0] == types[1])
                return this;
            else
                return new ProductType(new PrimSig[] {
                                                      types[1], types[0]
                });
        }

        /**
         * Returns the cross product of this and that.
         * <p>
         * Note: If either or both is NONE->..->NONE, then we return NONE->..->NONE
         * instead.
         */
        ProductType product(ProductType that) {
            final int n = types.length + that.types.length;
            if (n < 0)
                throw new OutOfMemoryError(); // This means the addition
                                             // overflowed!
            if (this.isEmpty())
                return (n == this.types.length) ? this : (new ProductType(n, NONE));
            if (that.isEmpty())
                return (n == that.types.length) ? that : (new ProductType(n, NONE));
            final PrimSig[] ans = new PrimSig[n];
            int j = 0;
            for (int i = 0; i < this.types.length; i++, j++) {
                ans[j] = this.types[i];
            }
            for (int i = 0; i < that.types.length; i++, j++) {
                ans[j] = that.types[i];
            }
            return new ProductType(ans);
        }

        /**
         * Returns the intersection of this and that.
         * <p>
         * Note: if (this[i] & that[i]) is empty for at least one i, then we return
         * "NONE->..->NONE" instead.
         * <p>
         * Precondition: this.arity == that.arity
         */
        private ProductType intersect(ProductType that) {
            if (isEmpty())
                return this;
            if (that.isEmpty())
                return that;
            final int n = types.length;
            final PrimSig[] ans = new PrimSig[n];
            for (int i = 0; i < n; i++) {
                PrimSig c = this.types[i].intersect(that.types[i]);
                if (c == NONE) {
                    for (i = 0; i < n; i++) {
                        ans[i] = c;
                    }
                    break;
                }
                ans[i] = c;
            }
            return new ProductType(ans);
        }

        /**
         * Returns true iff the intersection of this and that is nonempty.
         * <p>
         * Precondition: this.arity == that.arity
         */
        private boolean intersects(ProductType that) {
            for (int i = types.length - 1; i >= 0; i--)
                if (!types[i].intersects(that.types[i]))
                    return false;
            return true;
        }

        /**
         * Returns the relational join of this and that.
         * <p>
         * Note: if (this.rightmost() & that.leftmost()) is empty, we return
         * NONE->..->NONE instead.
         * <p>
         * Precondition: (this.arity > 0) && (that.arity > 0) && (this.arity!=1 ||
         * that.arity!=1)
         */
        ProductType join(ProductType that) {
            int left = types.length, right = that.types.length, n = left + right - 2;
            if (left <= 1 && right <= 1)
                return zero; // We try to do the best we can, in the face of
                            // precondition violation
            if (n < 0)
                throw new OutOfMemoryError(); // This means the addition
                                             // overflowed!
            final PrimSig a = types[left - 1], b = that.types[0], c = a.intersect(b);
            if (c == NONE)
                return new ProductType(n, c);
            final PrimSig[] types = new PrimSig[n];
            int j = 0;
            for (int i = 0; i < left - 1; i++, j++) {
                types[j] = this.types[i];
            }
            for (int i = 1; i < right; i++, j++) {
                types[j] = that.types[i];
            }
            return new ProductType(types);
        }

        /**
         * If (this[i] & that) is not empty, then return
         * this[0]->this[1]->this[2]->this[3]..->this[n-1] except the i-th entry is
         * replaced by (this[i] & that).
         * <p>
         * Otherwise, this method returns NONE->..->NONE
         */
        ProductType columnRestrict(PrimSig that, int i) {
            if (i < 0 || i >= types.length || isEmpty())
                return this;
            that = types[i].intersect(that);
            if (that == types[i])
                return this;
            if (that == NONE)
                return new ProductType(types.length, that);
            final PrimSig[] newlist = new PrimSig[types.length];
            for (int j = 0; j < types.length; j++) {
                newlist[j] = types[j];
            }
            newlist[i] = that;
            return new ProductType(newlist);
        }

        /**
         * Returns the String representation of this ProductType object.
         */
        @Override
        public String toString() {
            if (types.length == 0)
                return "";
            StringBuilder ans = new StringBuilder();
            for (int i = 0; i < types.length; i++) {
                if (i != 0)
                    ans.append("->");
                ans.append(types[i]);
            }
            return ans.toString();
        }
    }

    /**
     * Constant value with is_int==false, is_bool==false, and entries.size()==0.
     */
    public static final Type             EMPTY         = new Type(false, null, 0);

    // [AM]
    /*
     * Can't be final because it relies on a static Sig.SIGINT being initialized
     */
    private static Type                  SMALL_INT     = null;

    /**
     * Constant value with is_int==false, is_bool==true, and entries.size()==0.
     */
    public static final Type             FORMULA       = new Type(true, null, 0);

    /**
     * Constant value with is_int==true, is_bool==true, and entries.size()==0.
     */
    public static final Type             INTANDFORMULA = new Type(true, null, 0);

    /**
     * True if primitive integer value is a possible value in this type.
     */
    // private final boolean is_int;
    private boolean                      is_small_int;

    /**
     * True if primitive boolean value is a possible value in this type.
     */
    public final boolean                 is_bool;

    /**
     * Contains a summary of the arities in this type. <br>
     * The (1<<0) bitmask is nonzero iff arity X exists for some X>30 <br>
     * The (1<<1) bitmask is nonzero iff arity 1 exists <br>
     * The (1<<2) bitmask is nonzero iff arity 2 exists <br>
     * The (1<<3) bitmask is nonzero iff arity 3 exists <br>
     * ... <br>
     * The (1<<30) bitmask is nonzero iff arity 30 exists
     */
    private final int                    arities;

    /**
     * Contains the list of ProductType entries in this type.
     */
    private final ConstList<ProductType> entries;

    public boolean is_int() {
        return checkIntType();
    }

    public boolean is_small_int() {
        return is_int() && is_small_int;
    }

    private boolean checkIntType() {
        if (entries == null)
            return false;
        for (ProductType e : entries) {
            if (e.arity() == 1 && e.get(0) == Sig.SIGINT)
                return true;
        }
        return false;
    }

    public static Type smallIntType() {
        if (SMALL_INT == null) {
            SMALL_INT = make(Sig.SIGINT);
            SMALL_INT.is_small_int = true;
        }
        return SMALL_INT;
    }

    /**
     * Returns an iterator that iterates over the ProductType entries in this type.
     * <p>
     * This iterator will reject all modification requests.
     */
    @Override
    public Iterator<ProductType> iterator() {
        return entries.iterator();
    }

    /**
     * Merge "x" into the set of entries, then return the new arity bitmask. <br>
     * Precondition: entries and arities are consistent
     */
    private static int add(TempList<ProductType> entries, int arities, ProductType x) {
        if (x == null || x.types.length == 0)
            return arities;
        final int arity = x.types.length;
        // If x is subsumed by a ProductType in this, return. Likewise, remove
        // all entries in this that are subsumed by x.
        for (int n = entries.size(), i = n - 1; i >= 0; i--) {
            ProductType y = entries.get(i);
            if (y.types.length != arity)
                continue;
            if (x.isSubtypeOf(y))
                return arities;
            if (y.isSubtypeOf(x)) {
                n--;
                entries.set(i, entries.get(n)).remove(n);
            }
        }
        if (arity > 30)
            arities = arities | 1;
        else
            arities = arities | (1 << arity);
        entries.add(x);
        return arities;
    }

    /**
     * Create a new type consisting of the given set of entries, set of arities, and
     * the given is_int/is_bool values;
     * <p>
     * Precondition: entries and arities must be consistent
     */
    private Type(boolean is_bool, ConstList<ProductType> entries, int arities) {
        this.is_bool = is_bool;
        if (entries == null || entries.size() == 0 || arities == 0) {
            this.entries = ConstList.make();
            this.arities = 0;
        } else {
            this.entries = entries;
            this.arities = arities;
        }
    }

    /**
     * Create a new type consisting of the given set of entries, set of arities, and
     * the given is_int/is_bool values;
     * <p>
     * Precondition: entries and arities must be consistent
     */
    private static Type make(boolean is_bool, ConstList<ProductType> entries, int arities) {
        if (entries == null || entries.size() == 0 || arities == 0) {
            return is_bool ? FORMULA : EMPTY;
        }
        return new Type(is_bool, entries, arities);
    }

    /**
     * Create the type consisting of the given ProductType entry.
     */
    static Type make(ProductType productType) {
        int ar = productType.types.length;
        if (ar == 0)
            return EMPTY;
        return make(false, ConstList.make(1, productType), (ar > 30) ? 1 : (1 << ar));
    }

    /**
     * Create the type list[start]->list[start+1]->..->list[end-1] (If start<0,
     * end<0, end>list.size(), or start>=end, this method will return EMPTY)
     */
    static Type make(List<PrimSig> list, int start, int end) {
        if (start < 0 || end < 0 || start >= end || end > list.size())
            return EMPTY;
        PrimSig[] newlist = new PrimSig[end - start];
        for (int i = start, j = 0; i < end; i++, j++) {
            PrimSig x = list.get(i);
            if (x == NONE) {
                for (i = 0; i < newlist.length; i++)
                    newlist[i] = x;
                break;
            }
            newlist[j] = x;
        }
        return make(new ProductType(newlist));
    }

    /**
     * Create the type "sig"; this method promises it will not call any method or
     * read anything from "sig".
     */
    static Type make(PrimSig sig) {
        return make(new ProductType(sig));
    }

    /** Create the type "sig->sig". */
    static Type make2(PrimSig sig) {
        return make(new ProductType(2, sig));
    }

    /**
     * Create a new type that is the same as "old", except the "is_int" flag is set
     * to true.
     */
    // static Type makeInt(Type old) {
    // if (old.is_int()) return old; else return make(true, old.is_bool,
    // old.entries, old.arities);
    // }

    /**
     * Create a new type that is the same as "old", except the "is_bool" flag is set
     * to true.
     */
    static Type makeBool(Type old) {
        if (old.is_bool)
            return old;
        else
            return make(true, old.entries, old.arities);
    }

    /**
     * Create a new type that is the same as "old", except the "is_bool" and
     * "is_int" flags are both set to false.
     */
    public static Type removesBoolAndInt(Type old) {
        if (!old.is_bool && !old.is_int())
            return old;
        else
            return make(false, old.entries, old.arities);
    }

    /**
     * Returns true iff ((this subsumes that) and (that subsumes this))
     */
    @Override
    public boolean equals(Object that) {
        if (this == that)
            return true;
        if (!(that instanceof Type))
            return false;
        Type x = (Type) that;
        if (arities != x.arities || /* [AM] is_int() != x.is_int() || */is_bool != x.is_bool)
            return false;
        again1: for (ProductType aa : entries) {
            for (ProductType bb : x.entries)
                if (aa.types.length == bb.types.length && aa.isSubtypeOf(bb))
                    continue again1;
            return false;
        }
        again2: for (ProductType bb : x.entries) {
            for (ProductType aa : entries)
                if (aa.types.length == bb.types.length && bb.isSubtypeOf(aa))
                    continue again2;
            return false;
        }
        return true;
    }

    /** Returns a hash code consistent with equals() */
    @Override
    public int hashCode() {
        return arities * /* [AM] (is_int()?1732051:1) **/ (is_bool ? 314157 : 1);
    }

    /**
     * Returns true if this.size()==0 or every entry consists only of NONE.
     */
    public boolean hasNoTuple() {
        for (int i = entries.size() - 1; i >= 0; i--)
            if (!entries.get(i).isEmpty())
                return false;
        return true;
    }

    /**
     * Returns true if this.size()>0 and at least one entry consists of something
     * other than NONE.
     */
    public boolean hasTuple() {
        for (int i = entries.size() - 1; i >= 0; i--)
            if (!entries.get(i).isEmpty())
                return true;
        return false;
    }

    /**
     * Returns the number of ProductType entries in this type.
     */
    public int size() {
        return entries.size();
    }

    /**
     * Returns true iff this contains an entry of the given arity.
     */
    public boolean hasArity(int arity) {
        if (arity <= 30)
            return arity > 0 && ((arities & (1 << arity)) != 0);
        if ((arities & 1) != 0)
            for (int i = entries.size() - 1; i >= 0; i--)
                if (entries.get(i).types.length == arity)
                    return true;
        return false;
    }

    /**
     * If every entry has the same arity, that arity is returned; <br>
     * else if some entries have different arities, we return -1; <br>
     * else we return 0 (which only happens when there are no entries at all).
     */
    public int arity() {
        if (arities == 0)
            return 0;
        int ans = 0;
        if ((arities & 1) == 0) {
            for (int i = 1; i <= 30; i++)
                if ((arities & (1 << i)) != 0) {
                    if (ans == 0)
                        ans = i;
                    else
                        return -1;
                }
        } else {
            for (int j = entries.size() - 1; j >= 0; j--) {
                int i = entries.get(j).types.length;
                if (ans == 0)
                    ans = i;
                else if (ans != i)
                    return -1;
            }
        }
        return ans;
    }

    /**
     * Returns true if exists some A in this, some B in that, where
     * (A[0]&B[0]!=empty)
     * <p>
     * This method ignores the "is_int" and "is_bool" flags.
     */
    public boolean firstColumnOverlaps(Type that) {
        if ((arities | that.arities) != 0)
            for (ProductType a : this)
                for (ProductType b : that)
                    if (a.types[0].intersects(b.types[0]))
                        return true;
        return false;
    }

    /**
     * Returns true if exists some A in this, some B in that, where
     * (A.arity==B.arity, and A[0]&B[0]!=empty)
     * <p>
     * This method ignores the "is_int" and "is_bool" flags.
     */
    public boolean canOverride(Type that) {
        if ((arities & that.arities) != 0)
            for (ProductType a : this)
                for (ProductType b : that)
                    if (a.types.length == b.types.length && a.types[0].intersects(b.types[0]))
                        return true;
        return false;
    }

    /**
     * Returns true iff exists some A in this, some B in that, where
     * A.arity==B.arity
     */
    public boolean hasCommonArity(Type that) {
        if ((arities & 1) != 0 && (that.arities & 1) != 0) {
            if (((arities - 1) & (that.arities - 1)) != 0)
                return true;
            for (ProductType a : this)
                for (ProductType b : that)
                    if (a.types.length == b.types.length)
                        return true;
            return false;
        }
        return (arities & that.arities) != 0;
    }

    /**
     * Returns a new type { A->B | A is in this, and B is in that }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or that.size()==0, then result.size()==0
     */
    public Type product(Type that) {
        if ((arities | that.arities) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType a : this)
            for (ProductType b : that)
                aa = add(ee, aa, a.product(b));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns true iff { A&B | A is in this, and B is in that } can have tuples.
     */
    public boolean intersects(Type that) {
        if ((arities & that.arities) != 0)
            for (ProductType a : this)
                if (!a.isEmpty())
                    for (ProductType b : that)
                        if (a.types.length == b.types.length && !b.isEmpty() && a.intersects(b))
                            return true;
        return false;
    }

    /**
     * Returns a new type { A&B | A is in this, and B is in that }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or that.size()==0, or they do not have entries with same
     * arity, then result.size()==0
     */
    public Type intersect(Type that) {
        if ((arities & that.arities) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType a : this)
            for (ProductType b : that)
                if (a.types.length == b.types.length)
                    aa = add(ee, aa, a.intersect(b));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A&that | A is in this }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If (this.size()==0), or (that.arity is not in this), then result.size()==0
     */
    public Type intersect(ProductType that) {
        if (!hasArity(that.types.length))
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType a : this)
            if (a.types.length == that.types.length)
                aa = add(ee, aa, a.intersect(that));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | A is in this, or A is in that }
     * <p>
     * ReturnValue.is_int == this.is_int || that.is_int <br>
     * ReturnValue.is_bool == this.is_bool || that.is_bool
     * <p>
     * If this.size()==0 and that.size()==0, then result.size()==0
     * <p>
     * As a special guarantee: if that==null, then the merge() method just returns
     * the current object
     */
    public Type merge(Type that) {
        if (that == null)
            return this;
        if (is_bool == that.is_bool) {
            if (this.size() == 0)
                return that;
            if (that.size() == 0)
                return this;
        }
        TempList<ProductType> ee = new TempList<ProductType>(entries);
        int aa = arities;
        for (ProductType x : that)
            aa = add(ee, aa, x);
        return make(is_bool || that.is_bool, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | A is in this, or A == that }
     * <p>
     * ReturnValue.is_int == this.is_int <br>
     * ReturnValue.is_bool == this.is_bool
     */
    public Type merge(ProductType that) {
        TempList<ProductType> ee = new TempList<ProductType>(entries);
        int aa = add(ee, arities, that);
        return make(is_bool, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | A is in this, or A == that.subList(begin,end) }
     * <p>
     * ReturnValue.is_int == this.is_int <br>
     * ReturnValue.is_bool == this.is_bool
     */
    public Type merge(ProductType that, int begin, int end) {
        if (!(0 <= begin && begin < end && end <= that.types.length))
            return this;
        PrimSig[] array = new PrimSig[end - begin];
        for (int i = 0; i < array.length; i++) {
            array[i] = that.types[begin + i];
        }
        TempList<ProductType> ee = new TempList<ProductType>(entries);
        int aa = add(ee, arities, new ProductType(array));
        return make(is_bool, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | A is in this, or A == that }
     * <p>
     * ReturnValue.is_int == this.is_int <br>
     * ReturnValue.is_bool == this.is_bool
     */
    public Type merge(List<PrimSig> that) {
        if (that.size() == 0)
            return this;
        PrimSig[] array = new PrimSig[that.size()];
        for (int i = 0; i < array.length; i++) {
            array[i] = that.get(i);
            if (array[i] == NONE) {
                if (hasArity(array.length))
                    return this;
                for (i = 0; i < array.length; i++)
                    array[i] = NONE;
                break;
            }
        }
        TempList<ProductType> ee = new TempList<ProductType>(entries);
        int aa = add(ee, arities, new ProductType(array));
        return make(is_bool, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | (A is in this && A.arity in that) or (A is in that
     * && A.arity in this) }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0 or that.size()==0, then result.size()==0
     * <p>
     * Special promise: if the result would be identical to this, then we will
     * return "this" as-is, without constructing a new object
     */
    public Type unionWithCommonArity(Type that) {
        if ((arities & that.arities) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        if (this.size() > 0 && that.size() > 0) {
            // add() ensures that if x doesn't need to change "ee", then "ee"
            // will stay unchanged
            for (ProductType x : this)
                if (that.hasArity(x.types.length))
                    aa = add(ee, aa, x);
            for (ProductType x : that)
                if (this.hasArity(x.types.length))
                    aa = add(ee, aa, x);
        }
        // So now, if nothing changed, we want to return "this" as-is
        if (!is_int() && !is_bool && aa == this.arities && ee.size() == this.entries.size()) {
            for (int i = ee.size() - 1;; i--) {
                if (i < 0)
                    return this;
                if (ee.get(i) != this.entries.get(i))
                    break;
            }
        }
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | (A is in this && A.arity in that) }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0 or that.size()==0, then result.size()==0
     */
    public Type pickCommonArity(Type that) {
        if (!is_int() && !is_bool && (arities & 1) == 0 && (arities & that.arities) == arities)
            return this;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        if ((arities & 1) == 0) {
            for (ProductType x : entries) {
                int xa = 1 << x.types.length;
                if ((that.arities & xa) != 0) {
                    aa = (aa | xa);
                    ee.add(x);
                }
            }
        } else {
            for (ProductType x : entries)
                if (that.hasArity(x.types.length))
                    aa = add(ee, aa, x);
        }
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A in this | A.artiy==1 }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or does not contain any ProductType entries of the given
     * arity, then result.size()==0
     */
    public Type pickUnary() {
        if ((arities & (1 << 1)) == 0)
            return EMPTY;
        if (!is_int() && !is_bool && arities == (1 << 1))
            return this;
        TempList<ProductType> ee = new TempList<ProductType>();
        for (ProductType x : entries)
            if (x.types.length == 1)
                ee.add(x);
        return make(false, ee.makeConst(), (1 << 1));
    }

    /**
     * Returns a new type { A in this | A.artiy==2 }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or does not contain any ProductType entries of the given
     * arity, then result.size()==0
     */
    public Type pickBinary() {
        if ((arities & (1 << 2)) == 0)
            return EMPTY;
        if (!is_int() && !is_bool && arities == (1 << 2))
            return this;
        TempList<ProductType> ee = new TempList<ProductType>();
        for (ProductType x : entries)
            if (x.types.length == 2)
                ee.add(x);
        return make(false, ee.makeConst(), (1 << 2));
    }

    /**
     * Returns a new type { A | A is binary and ~A is in this }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or does not contain any binary ProductType entries, then
     * result.size()==0
     */
    public Type transpose() {
        if ((arities & (1 << 2)) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType a : this)
            if (a.types.length == 2)
                aa = add(ee, aa, a.transpose());
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns true if for all A in this, there exists B in that, where A is equal
     * or subset of B.
     * <p>
     * Note: if this.is_int && !that.is_int, we return false immediately.
     * <p>
     * Note: if this.is_bool && !that.is_bool, we return false immediately.
     * <p>
     * Note: if this nothing above is violated, and this type has no relational
     * entry in it, we return true.
     */
    public boolean isSubtypeOf(Type that) {
        if (this == that)
            return true;
        if (is_int() && !that.is_int())
            return false;
        if (is_bool && !that.is_bool)
            return false;
        List<List<PrimSig>> those = that.fold();
        again: for (ProductType a : this) {
            for (List<PrimSig> b : those)
                if (a.arity() == b.size() && a.isSubtypeOf(b))
                    continue again;
            return false;
        }
        return true;
    }

    /**
     * Returns a new type { A.B | exists A in this, exists B in that, where
     * A.arity+B.arity>2 }
     * <p>
     * If this.size()==0, or that.size()==0, or none of the entries have the right
     * arity, then result.size()==0.
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     */
    public Type join(Type that) {
        if (size() == 0 || that.size() == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType a : this)
            for (ProductType b : that)
                if (a.types.length > 1 || b.types.length > 1)
                    aa = add(ee, aa, a.join(b));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { R[0]->..->R[n-1] | exists n-ary A in this, exists unary
     * B in that, such that R[i]==A[i] except R[0]==(A[0] & B)
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or that does not contain any unary entry, then
     * result.size()==0
     */
    public Type domainRestrict(Type that) {
        if (size() == 0 || (that.arities & (1 << 1)) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType b : that)
            if (b.types.length == 1)
                for (ProductType a : this)
                    aa = add(ee, aa, a.columnRestrict(b.types[0], 0));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { R[0]->..->R[n-1] | exists n-ary A in this, exists unary
     * B in that, such that R[i]==A[i] except R[n-1]==(A[n-1] & B)
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If this.size()==0, or that does not contain any unary entry, then
     * result.size()==0
     */
    public Type rangeRestrict(Type that) {
        if (size() == 0 || (that.arities & (1 << 1)) == 0)
            return EMPTY;
        TempList<ProductType> ee = new TempList<ProductType>();
        int aa = 0;
        for (ProductType b : that)
            if (b.types.length == 1)
                for (ProductType a : this)
                    aa = add(ee, aa, a.columnRestrict(b.types[0], a.types.length - 1));
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type { A | (A in this) and (A.arity == arity) }
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If it does not contain any entry with the given arity, then result.size()==0
     */
    public Type extract(int arity) {
        final int aa = (arity > 30 ? 1 : (1 << arity));
        if (!is_bool && !is_int() && arity <= 30 && arities == aa)
            return this;
        if ((arities & aa) == 0)
            return EMPTY;
        final TempList<ProductType> ee = new TempList<ProductType>();
        for (ProductType x : entries)
            if (x.types.length == arity)
                ee.add(x);
        return make(false, ee.makeConst(), aa);
    }

    /**
     * Returns a new type u + u.u + u.u.u + ... (where u == the set of binary
     * entries in this type)
     * <p>
     * ReturnValue.is_int == false <br>
     * ReturnValue.is_bool == false
     * <p>
     * If it does not contain any binary entries, then result.size()==0
     */
    public Type closure() {
        Type ans = extract(2);
        Type u = ans;
        Type uu = u;
        while (true) {
            uu = uu.join(u);
            Type oldans = ans;
            ans = ans.unionWithCommonArity(uu);
            if (oldans == ans)
                break; // The special guarantee of unionWithCommonArity()
                      // allows us to use the cheaper "oldans==ans" here
                      // instead of doing the more expensive
                      // "oldans.equals(ans)"
        }
        return ans;
    }

    Type __closure_old_bug() {
        Type ans = extract(2), u = ans, uu = u.join(u);
        while (uu.hasTuple()) {
            Type oldans = ans, olduu = uu;
            ans = ans.unionWithCommonArity(uu);
            uu = uu.join(u);
            // [AM] olduu.equals(uu) never gets satisfied in some cases (e.g.,
            // when the union type
            // contains tuples that are mutually recursive, for instance {S->T,
            // T->S}
            if (oldans == ans && olduu.equals(uu))
                break;
            // The special guarantee of unionWithCommonArity() allows us to use
            // the cheaper "oldans==ans" here
            // instead of doing the more expensive "oldans.equals(ans)"
        }
        return ans;
    }

    /**
     * Convert this type into a UNION of PRODUCT of sigs.
     *
     * @throws ErrorType if it does not contain exactly one arity
     * @throws ErrorType if is_int is true
     * @throws ErrorType if is_bool is true
     */
    public Expr toExpr() throws Err {
        int arity = arity();
        if (is_bool || arity < 1)
            throw new ErrorType("Cannot convert this type into a bounding expression.");
        Expr ans = null;
        for (ProductType pt : this) {
            Expr pro = null;
            for (int i = 0; i < arity; i++)
                if (pro == null)
                    pro = pt.types[i];
                else
                    pro = pro.product(pt.types[i]);
            if (ans == null)
                ans = pro;
            else
                ans = ans.plus(pro);
        }
        return ans;
    }

    /**
     * Merge "a" into the set of entries.
     * <p>
     * If {a}+this.entries contain a set of entries X1..Xn, such that <br>
     * (1) For each X: X[j]==a[j] for i!=j, and X[i].super==a[i].super <br>
     * (2) X1[i]..Xn[i] exhaust all the direct subsignatures of an abstract parent
     * sig <br>
     * THEN: <br>
     * we remove X1..Xn, then return the merged result of X1..Xn <br>
     * ELSE <br>
     * we change nothing, and simply return null
     * <p>
     * <b>Precondition:</b> a[i] is not NONE, and a[i].parent is abstract, and
     * a[i].parent!=UNIV
     */
    private static List<PrimSig> fold(ArrayList<List<PrimSig>> entries, List<PrimSig> a, int i) {
        PrimSig parent = a.get(i).parent;
        SafeList<PrimSig> children;
        try {
            children = parent.children();
        } catch (Err ex) {
            return null;
        } // Exception only occurs if a[i].parent==UNIV
        List<PrimSig> subs = children.makeCopy();
        ArrayList<List<PrimSig>> toDelete = new ArrayList<List<PrimSig>>();
        for (int bi = entries.size() - 1; bi >= 0; bi--) {
            List<PrimSig> b = entries.get(bi);
            if (b.size() == a.size()) {
                for (int j = 0;; j++) {
                    if (j >= b.size()) {
                        toDelete.add(b);
                        subs.remove(b.get(i));
                        break;
                    }
                    PrimSig bt1 = a.get(j), bt2 = b.get(j);
                    if (i == j && bt2.parent != parent)
                        break;
                    if (i != j && bt2 != bt1)
                        break;
                }
            }
        }
        subs.remove(a.get(i));
        if (subs.size() != 0)
            return null;
        entries.removeAll(toDelete);
        entries.remove(a);
        a = new ArrayList<PrimSig>(a);
        a.set(i, parent);
        return a;
    }

    /**
     * Return the result of folding this Type (that is, whenever a subset of
     * relations are identical except for 1 position, where together they comprise
     * of all direct subsigs of an abstract sig, then we merge them)
     * <p>
     * Note: the result is only current with respect to the current existing sig
     * objects
     */
    public List<List<PrimSig>> fold() {
        ArrayList<List<PrimSig>> e = new ArrayList<List<PrimSig>>();
        for (ProductType xx : entries) {
            List<PrimSig> x = Arrays.asList(xx.types);
            while (true) {
                int n = x.size();
                boolean changed = false;
                for (int i = 0; i < n; i++) {
                    PrimSig bt = x.get(i);
                    if (bt.parent != null && bt.parent != UNIV && bt.parent.isAbstract != null) {
                        List<PrimSig> folded = fold(e, x, i);
                        if (folded != null) {
                            x = folded;
                            changed = true;
                            i--;
                        }
                    }
                }
                if (changed == false)
                    break;
            }
            e.add(x);
        }
        return e;
    }

    /** Returns a human-readable description of this type. */
    @Override
    public String toString() {
        boolean first = true;
        StringBuilder ans = new StringBuilder("{");
        // [AM] if (is_int()) { first=false; ans.append("PrimitiveInteger"); }
        if (is_bool) {
            if (!first)
                ans.append(", ");
            first = false;
            ans.append("PrimitiveBoolean");
        }
        for (List<PrimSig> r : fold()) {
            if (!first)
                ans.append(", ");
            first = false;
            for (int i = 0; i < r.size(); i++) {
                if (i != 0)
                    ans.append("->");
                ans.append(r.get(i));
            }
        }
        return ans.append('}').toString();
    }

    @Override
    public Pos pos() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String explain() {
        StringBuilder sb = new StringBuilder();
        String del = "";
        for (ProductType t : this) {
            sb.append(del);
            sb.append(t.toString());
            del = "->";
        }
        return sb.toString();
    }
}
