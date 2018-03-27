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

import java.util.Iterator;

import kodkod.engine.fol2sat.Environment;
import kodkod.util.collections.Containers;
import kodkod.util.ints.ArraySequence;
import kodkod.util.ints.HomogenousSequence;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.ints.RangeSequence;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * <p>
 * An n-dimensional matrix of {@link kodkod.engine.bool.BooleanValue boolean
 * values}. Boolean matrices are indexed using flat integer indeces. For
 * example, let m be a the 2 x 3 matrix of boolean variables identifed by labels
 * [0 4 1; 5 10 2]. Then, m[0] = 0, m[3] = 5, m[5] = 2, etc.
 * </p>
 * <p>
 * All values stored in the same matrix must be created by the same
 * {@link kodkod.engine.bool.BooleanFactory circuit factory}. All methods that
 * accept another BooleanMatrix as an input will throw an
 * IllegalArgumentException if the values in the input matrix do not belong to
 * the same factory as the values in the receiver matrix.
 * </p>
 * <p>
 * Some instances can store only constant values, or can only store values at
 * particular indices (see
 * {@link kodkod.engine.bool.BooleanFactory#matrix(Dimensions, IntSet, IntSet)}).
 * If this is the case, an attempt to call {@link #set(int, BooleanValue) } with
 * invalid parameters will cause an IllegalArgumentException or an
 * IndexOutOfBoundsException.
 * </p>
 *
 * @specfield dimensions: Dimensions
 * @specfield factory: BooleanFactory
 * @specfield elements: [0..dimensions.capacity) -> one factory.components
 * @author Emina Torlak
 */
public final class BooleanMatrix implements Iterable<IndexedEntry<BooleanValue>>, Cloneable {

    private IDefCond                           defCond = new DefCond();

    private final Dimensions                   dims;
    private final BooleanFactory               factory;
    private final SparseSequence<BooleanValue> cells;

    /**
     * Constructs a new matrix with the given dimensions, factory, and entries.
     *
     * @requires dimensions != null && factory != null && seq != null
     * @requires seq.indices() in [0..dimensions.capacity)
     * @ensures this.dimensions' = dimensions && this.factory' = factory &&
     *          this.elements' = [0..dimensions.capacity)->one FALSE
     */
    private BooleanMatrix(Dimensions dimensions, BooleanFactory factory, SparseSequence<BooleanValue> seq) {
        this.dims = dimensions;
        this.factory = factory;
        this.cells = seq;
    }

    /**
     * Constructs a new matrix with the given dimensions and factory, backed by a
     * sparse sequence which can most efficiently hold the elements storable in the
     * sparse sequences s0 and s1.
     *
     * @ensures this.dimensions' = dimensions && this.factory' = factory &&
     *          this.elements' = [0..dimensions.capacity)->one FALSE
     */
    private BooleanMatrix(Dimensions d, BooleanFactory f, SparseSequence<BooleanValue> s0, SparseSequence<BooleanValue> s1) {
        this.dims = d;
        this.factory = f;
        final Class< ? > c0 = s0.getClass(), c1 = s1.getClass();
        if (c0 != c1 || c0 == RangeSequence.class)
            this.cells = new RangeSequence<BooleanValue>();
        else if (c0 == HomogenousSequence.class)
            this.cells = new HomogenousSequence<BooleanValue>(TRUE, Ints.bestSet(d.capacity()));
        else
            this.cells = new TreeSequence<BooleanValue>();
    }

    /**
     * Constructs a new matrix with the given dimensions and factory, backed by a
     * sparse sequence which can most efficiently hold the elements storable in the
     * matrices m and rest.
     *
     * @requires null !in d + m + rest[int]
     * @requires m.factory = rest[int].factory
     * @requires d.equals(m.dims) => d.equals(rest[int].dims)
     * @ensures this.dimensions' = dimensions && this.factory' = m.factory &&
     *          this.elements' = [0..dimensions.capacity)->one FALSE
     * @throws IllegalArgumentException m.factory != rest[int].factory
     * @throws IllegalArgumentException !(d.equals(m.dims) =>
     *             d.equals(rest[int].dims))
     */
    private BooleanMatrix(Dimensions d, BooleanMatrix m, BooleanMatrix... rest) {
        this.dims = d;
        this.factory = m.factory;

        final Class< ? > h = HomogenousSequence.class, t = TreeSequence.class;
        final boolean sameDim = d.equals(m);

        Class< ? > c = m.cells.getClass();
        int cId = c == h ? 1 : c == t ? 2 : 4;

        for (BooleanMatrix other : rest) {
            checkFactory(factory, other.factory);
            if (sameDim)
                checkDimensions(d, other.dims);

            c = other.cells.getClass();
            cId |= c == h ? 1 : c == t ? 2 : 4;
        }

        switch (cId) {
            case 1 :
                this.cells = new HomogenousSequence<BooleanValue>(TRUE, Ints.bestSet(d.capacity()));
                break;
            case 2 :
                this.cells = new TreeSequence<BooleanValue>();
                break;
            default :
                this.cells = new RangeSequence<BooleanValue>();
        }

        mergeDefConds(m);
        mergeDefConds(rest);
    }

    /**
     * Constructs a new matrix with the given dimensions and factory. The
     * constructed matrix can store any kind of BooleanValue.
     *
     * @requires dimensions != null && factory != null
     * @ensures this.dimensions' = dimensions && this.factory' = factory &&
     *          this.elements' = [0..dimensions.capacity)->one FALSE
     */
    BooleanMatrix(Dimensions dims, BooleanFactory factory) {
        this.dims = dims;
        this.factory = factory;
        this.cells = new RangeSequence<BooleanValue>();
    }

    /**
     * Constructs a new matrix with the given dimensions and factory, and
     * initializes the indices in the given set to TRUE. The constructed matrix will
     * be capable of storing only constants iff trueIndeces.equals(allIndices).
     * Otherwise, it will be able to store any kind of BooleanValue ONLY at the
     * indices given by allIndices. Any attempt to call
     * {@link #set(int, BooleanValue) } on an index outside of allIndices may result
     * in an IndexOutOfBoundsException.
     *
     * @requires allIndices.containsAll(trueIndices)
     * @requires trueIndices is not modifiable using an external handle
     * @requires dimensions != null && factory != null && trueIndices != null &&
     *           allIndices != null
     * @requires dimensions.validate(allIndices.min()) &&
     *           dimensions.validate(allIndices.max())
     * @ensures this.dimensions' = dimensions && this.factory' = factory &&
     *          this.elements' = [0..dimensions.capacity)->one FALSE ++ trueIndices
     *          -> one TRUE
     */
    BooleanMatrix(Dimensions dims, BooleanFactory factory, IntSet allIndices, IntSet trueIndices) {
        this.dims = dims;
        this.factory = factory;
        final int tsize = trueIndices.size(), asize = allIndices.size();
        if (tsize == asize)
            this.cells = new HomogenousSequence<BooleanValue>(TRUE, trueIndices);
        else {
            this.cells = tsize == 0 || asize / tsize >= 2 ? new ArraySequence<BooleanValue>(allIndices) : new RangeSequence<BooleanValue>();
            for (IntIterator iter = trueIndices.iterator(); iter.hasNext();) {
                cells.put(iter.next(), TRUE);
            }
        }
    }

    private void mergeDefConds(BooleanMatrix... bms) {
        mergeDefConds(FALSE, bms);
    }

    private void mergeDefConds(BooleanValue of, BooleanMatrix... bms) {
        IDefCond[] dcs = new IDefCond[1 + bms.length];
        dcs[0] = this.defCond();
        for (int i = 0; i < bms.length; i++) {
            dcs[i + 1] = bms[i].defCond();
            this.defCond().addVars(bms[i].defCond().vars());
        }
        this.defCond().setOverflows(of, DefCond.merge(factory, dcs));
    }

    /**
     * Returns the dimensions of this matrix.
     *
     * @return this.dimensions
     */
    public final Dimensions dimensions() {
        return dims;
    }

    /**
     * Returns the factory used to construct all the non-constant entries in this
     * matrix.
     *
     * @return this.factory
     */
    public final BooleanFactory factory() {
        return factory;
    }

    /**
     * Returns this.defCond
     *
     * @return this.defCond
     */
    public final IDefCond defCond() {
        return defCond;
    }

    public void setDefCond(IDefCond dc) {
        this.defCond = dc;
    }

    /**
     * Returns the number of non-FALSE entries in this matrix.
     *
     * @return #this.elements.(BooleanValue - FALSE)
     */
    public final int density() {
        return cells.size();
    }

    /**
     * Returns an IndexedEntry-based view of the non-FALSE entries in this matrix.
     * The returned iterator enumerates indexed entries that represent the non-FALSE
     * entries in the matrix, in the ascending order of indeces. For example,
     * suppose that the elements of this are 0->FALSE, 1->(a & b), 2->FALSE, 3->(c |
     * d). Then, the Iterator will return two IndexedEntries, c1 then c2, such that
     * c1.index=1 && c1.value = a & b and c2.index=3 && c.value = c | d. Calling
     * {@link Iterator#remove()} on the returned iterator has the same effect as
     * setting the entry obtained through the last call to {@link Iterator#next()}
     * to FALSE.
     *
     * @return an iterator over IndexedEntries representing the non-FALSE entries in
     *         this matrix.
     */
    @Override
    public final Iterator<IndexedEntry<BooleanValue>> iterator() {
        return cells.iterator();
    }

    /**
     * Returns the set of all indices in this matrix that contain non-FALSE values.
     *
     * @return the set of all indices in this matrix that contain non-FALSE values.
     */
    public final IntSet denseIndices() {
        return cells.indices();
    }

    /**
     * Return FALSE if value is null; otherwise return value itself.
     *
     * @return FALSE if value is null; otherwise return value itself.
     */
    private final BooleanValue maskNull(BooleanValue value) {
        return value == null ? FALSE : value;
    }

    /**
     * Returns the value at the given index, without checking that the index is in
     * bounds.
     *
     * @return this.elements[index]
     */
    private final BooleanValue fastGet(final int index) {
        return maskNull(cells.get(index));
    }

    /**
     * Returns the element at the specified index.
     *
     * @return this.elements[index]
     * @throws IndexOutOfBoundsException index < 0 || index >=
     *             this.dimensions.capacity
     */
    public final BooleanValue get(final int index) {
        if (!dims.validate(index))
            throw new IndexOutOfBoundsException(index + " is not a valid index.");
        return maskNull(cells.get(index));
    }

    /**
     * Returns a new matrix each of whose entries is a negation of the corresponding
     * entry in this matrix.
     *
     * @return { m: BooleanMatrix | m.dimensions=this.dimensions && m.factory =
     *         this.factory && all i: [0..m.dimensions.capacity) | m.elements[i] =
     *         !this.elements[i] }
     */
    public final BooleanMatrix not() {
        final BooleanMatrix negation = new BooleanMatrix(dims, factory, cells, cells);
        negation.mergeDefConds(this);

        for (int i = 0, max = dims.capacity(); i < max; i++) {
            BooleanValue v = cells.get(i);
            if (v == null)
                negation.cells.put(i, TRUE);
            else if (v != TRUE)
                negation.cells.put(i, v.negation());
        }

        return negation;
    }

    /**
     * @throws IllegalArgumentException f != this.factory
     */
    private static final void checkFactory(BooleanFactory f0, BooleanFactory f1) {
        if (f0 != f1)
            throw new IllegalArgumentException("Incompatible factories: " + f0 + " and " + f1);
    }

    /**
     * @throws IllegalArgumentException !d0.equals(d1)
     */
    private static final void checkDimensions(Dimensions d0, Dimensions d1) {
        if (!d0.equals(d1))
            throw new IllegalArgumentException("Incompatible dimensions: " + d0 + " and " + d1);
    }

    /**
     * Returns a new matrix such that an entry in the returned matrix represents a
     * conjunction of the corresponding entries in this and other matrix. The effect
     * of this method is the same as calling this.compose(ExprOperator.Binary.AND,
     * other).
     *
     * @return { m: BooleanMatrix | m.dimensions = this.dimensions && m.factory =
     *         this.factory && all i: [0..m.dimensions.capacity) | m.elements[i] =
     *         this.elements[i] AND other.elements[i] }
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanMatrix and(BooleanMatrix other) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);

        final BooleanMatrix ret = new BooleanMatrix(dims, factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        final SparseSequence<BooleanValue> s1 = other.cells;
        if (cells.isEmpty() || s1.isEmpty())
            return ret;
        for (IndexedEntry<BooleanValue> e0 : cells) {
            BooleanValue v1 = s1.get(e0.index());
            if (v1 != null)
                ret.fastSet(e0.index(), factory.and(e0.value(), v1));
        }
        return ret;
    }

    /**
     * Returns a new matrix such that an entry in the returned matrix represents a
     * conjunction of the corresponding entries in this and other matrices.
     *
     * @requires all i: [0..others.length) | others[i].dimensions = this.dimensions
     *           && others[i].factory = this.factory
     * @return others.length = 0 => m else { m: BooleanMatrix | m.dimensions =
     *         this.dimensions && m.factory = this.factory && all i:
     *         [0..m.dimensions.capacity) | m.elements[i] = AND(this.elements[i],
     *         others[int].elements[i]) }
     * @throws NullPointerException others = null
     * @throws IllegalArgumentException some m: others[int] |
     *             !m.dimensions.equals(this.dimensions) || m.factory !=
     *             this.factory
     */
    public final BooleanMatrix and(final BooleanMatrix... others) {
        final BooleanMatrix ret = new BooleanMatrix(dims, this, others);

        for (IndexedEntry<BooleanValue> cell : cells) {
            final BooleanAccumulator acc = BooleanAccumulator.treeGate(AND, cell.value());
            for (BooleanMatrix other : others) {
                if (acc.add(other.fastGet(cell.index())) == BooleanConstant.FALSE)
                    break;
            }
            if (!acc.isShortCircuited()) {
                ret.fastSet(cell.index(), factory.accumulate(acc));
            }
        }
        return ret;
    }

    /**
     * Returns a new matrix such that an entry in the returned matrix represents a
     * combination of the corresponding entries in this and other matrix. The effect
     * of this method is the same as calling this.compose(ExprOperator.Binary.OR,
     * other).
     *
     * @return { m: BooleanMatrix | m.dimensions = this.dimensions && m.factory =
     *         this.factory && all i: [0..m.dimensions.capacity) | m.elements[i] =
     *         this.elements[i] OR other.elements[i] }
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanMatrix or(BooleanMatrix other) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);
        if (this.cells.isEmpty())
            return other.clone();
        else if (other.cells.isEmpty())
            return this.clone();

        final BooleanMatrix ret = new BooleanMatrix(dims, factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        final SparseSequence<BooleanValue> retSeq = ret.cells;
        for (IndexedEntry<BooleanValue> e0 : cells) {
            BooleanValue v1 = other.cells.get(e0.index());
            if (v1 == null)
                retSeq.put(e0.index(), e0.value());
            else
                retSeq.put(e0.index(), factory.or(e0.value(), v1));
        }
        for (IndexedEntry<BooleanValue> e1 : other.cells) {
            if (!cells.containsIndex(e1.index()))
                retSeq.put(e1.index(), e1.value());
        }
        return ret;
    }

    /**
     * Returns a new matrix such that an entry in the returned matrix represents a
     * disjunction of the corresponding entries in this and other matrices.
     *
     * @requires all i: [0..others.length) | others[i].dimensions = this.dimensions
     *           && others[i].factory = this.factory
     * @return others.length = 0 => m else { m: BooleanMatrix | m.dimensions =
     *         this.dimensions && m.factory = this.factory && all i:
     *         [0..m.dimensions.capacity) | m.elements[i] = OR(this.elements[i],
     *         others[int].elements[i]) }
     * @throws NullPointerException others = null
     * @throws IllegalArgumentException some m: others[int] |
     *             !m.dimensions.equals(this.dimensions) || m.factory !=
     *             this.factory
     */
    public final BooleanMatrix or(final BooleanMatrix... others) {
        final BooleanMatrix ret = new BooleanMatrix(dims, this, others);

        for (IndexedEntry<BooleanValue> cell : cells) {
            final BooleanAccumulator acc = BooleanAccumulator.treeGate(OR, cell.value());
            for (BooleanMatrix other : others) {
                if (acc.add(other.fastGet(cell.index())) == BooleanConstant.TRUE)
                    break;
            }
            ret.fastSet(cell.index(), factory.accumulate(acc));
        }

        for (int i = 0, length = others.length; i < length; i++) {
            for (IndexedEntry<BooleanValue> cell : others[i].cells) {
                if (ret.cells.containsIndex(cell.index()))
                    continue;
                final BooleanAccumulator acc = BooleanAccumulator.treeGate(OR, cell.value());
                for (int j = i + 1; j < length; j++) {
                    if (acc.add(others[j].fastGet(cell.index())) == BooleanConstant.TRUE)
                        break;
                }
                ret.fastSet(cell.index(), factory.accumulate(acc));
            }
        }

        return ret;
    }

    /**
     * Returns the cross product of this and other matrix, using conjunction instead
     * of multiplication.
     *
     * @return { m: BooleanMatrix | m = this x other }
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException this.factory != other.factory
     */
    public final BooleanMatrix cross(final BooleanMatrix other) {
        checkFactory(this.factory, other.factory);

        final BooleanMatrix ret = new BooleanMatrix(dims.cross(other.dims), factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        if (cells.isEmpty() || other.cells.isEmpty())
            return ret;

        final int ocap = other.dims.capacity();
        for (IndexedEntry<BooleanValue> e0 : cells) {
            int i = ocap * e0.index();
            for (IndexedEntry<BooleanValue> e1 : other.cells) {
                BooleanValue conjunction = factory.and(e0.value(), e1.value());
                if (conjunction != FALSE)
                    ret.cells.put(i + e1.index(), conjunction);
            }
        }

        return ret;
    }

    /**
     * Updates the itrs and idxs arrays for the next step of the cross-product
     * computation and returns a partial index based on the updated idxs values.
     *
     * @requires matrices.length = itrs.length = idxs.length
     * @requires all m: matrices[int] | m.density() > 0
     * @requires currentIdx is a partial index based on the current value of idxs
     * @ensures updates the itrs and idxs arrays for the next step cross-product
     *          computation
     * @return a partial index based on the freshly updated idxs values.
     */
    private static int nextCross(final BooleanMatrix[] matrices, final IntIterator[] itrs, final int[] idxs, int currentIdx) {

        int mult = 1;
        for (int i = itrs.length - 1; i >= 0; i--) {
            if (itrs[i].hasNext()) {
                final int old = idxs[i];
                idxs[i] = itrs[i].next();
                return currentIdx - mult * old + mult * idxs[i];
            } else {
                itrs[i] = matrices[i].cells.indices().iterator();
                final int old = idxs[i];
                idxs[i] = itrs[i].next();
                currentIdx = currentIdx - mult * old + mult * idxs[i];
                mult *= matrices[i].dims.capacity();
            }
        }

        return -1;
    }

    /**
     * Initializes the itrs and idxs arrays for cross-product computation and
     * returns a partial index based on the freshly computed idxs values.
     *
     * @requires matrices.length = itrs.length = idxs.length
     * @requires all m: matrices[int] | m.density() > 0
     * @ensures initializes the itrs and idxs arrays for cross-product computation
     * @return a partial index based on the freshly computed idxs values.
     */
    private static int initCross(final BooleanMatrix[] matrices, final IntIterator[] itrs, final int[] idxs) {
        int mult = 1, idx = 0;
        for (int i = matrices.length - 1; i >= 0; i--) {
            itrs[i] = matrices[i].cells.indices().iterator();
            idxs[i] = itrs[i].next();
            idx += mult * idxs[i];
            mult *= matrices[i].dims.capacity();
        }
        return idx;
    }

    /**
     * Returns the cross product of this and other matrices, using conjunction
     * instead of multiplication.
     *
     * @requires this.factory = others[int].factory
     * @return others.length=0 => { m: BooleanMatrix | m.dimensions =
     *         this.dimensions && no m.elements } else { m: BooleanMatrix | m = this
     *         x others[0] x ... x others[others.length-1] }
     * @throws NullPointerException others = null
     * @throws IllegalArgumentException this.factory != others[int].factory
     */
    public final BooleanMatrix cross(final BooleanMatrix... others) {
        Dimensions retDims = dims;
        boolean empty = cells.isEmpty();
        for (BooleanMatrix other : others) {
            retDims = retDims.cross(other.dims);
            empty = empty || other.cells.isEmpty();
        }

        final BooleanMatrix ret = new BooleanMatrix(retDims, this, others);
        if (empty)
            return ret;

        final IntIterator[] itrs = new IntIterator[others.length];
        final int[] otherIdxs = new int[others.length];

        final int ocap = retDims.capacity() / dims.capacity();

        for (IndexedEntry<BooleanValue> cell : cells) {
            final int idx = ocap * cell.index();
            for (int restIdx = initCross(others, itrs, otherIdxs); restIdx >= 0; restIdx = nextCross(others, itrs, otherIdxs, restIdx)) {
                final BooleanAccumulator acc = BooleanAccumulator.treeGate(AND, cell.value());
                for (int i = others.length - 1; i >= 0; i--) {
                    if (acc.add(others[i].fastGet(otherIdxs[i])) == BooleanConstant.FALSE)
                        break;
                }
                if (!acc.isShortCircuited()) {
                    ret.fastSet(idx + restIdx, factory.accumulate(acc));
                }
            }

        }

        return ret;
    }

    /**
     * Sets the value at the specified index to the given value; returns the value
     * previously at the specified position. It performs no index or null checking.
     *
     * @ensures this.elements'[index] = formula
     */
    private final void fastSet(final int index, final BooleanValue formula) {
        if (formula == FALSE)
            cells.remove(index);
        else
            cells.put(index, formula);
    }

    /**
     * Returns the dot product of this and other matrix, using conjunction instead
     * of multiplication and disjunction instead of addition.
     *
     * @return { m: BooleanMatrix | m = this*other }
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException this.factory != other.factory
     * @throws IllegalArgumentException dimensions incompatible for multiplication
     */
    public final BooleanMatrix dot(final BooleanMatrix other) {
        checkFactory(this.factory, other.factory);

        final BooleanMatrix ret = new BooleanMatrix(dims.dot(other.dims), factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        if (cells.isEmpty() || other.cells.isEmpty())
            return ret;

        final SparseSequence<BooleanValue> mutableCells = ret.clone().cells;
        final int b = other.dims.dimension(0);
        final int c = other.dims.capacity() / b;

        for (IndexedEntry<BooleanValue> e0 : cells) {
            int i = e0.index();
            BooleanValue iVal = e0.value();
            int rowHead = (i % b) * c, rowTail = rowHead + c - 1;
            for (Iterator<IndexedEntry<BooleanValue>> iter1 = other.cells.iterator(rowHead, rowTail); iter1.hasNext();) {
                IndexedEntry<BooleanValue> e1 = iter1.next();
                BooleanValue retVal = factory.and(iVal, e1.value());
                if (retVal != FALSE) {
                    int k = (i / b) * c + e1.index() % c;
                    if (retVal == TRUE)
                        mutableCells.put(k, TRUE);
                    else {
                        BooleanValue kVal = mutableCells.get(k);
                        if (kVal != TRUE) {
                            if (kVal == null) {
                                kVal = BooleanAccumulator.treeGate(OR);
                                mutableCells.put(k, kVal);
                            }
                            ((BooleanAccumulator) kVal).add(retVal);
                        }
                    }
                }
            }
        }

        // make mutable gates immutable
        for (IndexedEntry<BooleanValue> e : mutableCells) {
            if (e.value() != TRUE) {
                ret.fastSet(e.index(), factory.accumulate((BooleanAccumulator) e.value()));
            } else {
                ret.fastSet(e.index(), TRUE);
            }
        }

        return ret;
    }

    /**
     * Returns a formula stating that the entries in this matrix are a subset of the
     * entries in the given matrix; i.e. the value of every entry in this matrix
     * implies the value of the corresponding entry in the given matrix.
     *
     * @return { f: BooleanValue | f <=> (this.elements[0]=>other.elements[0]) AND
     *         ... AND
     *         (this.elements[this.dimensions.capacity-1]=>other.elements[this.dimensions.capacity-1]))
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanValue subset(BooleanMatrix other, Environment< ? , ? > env) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);
        final BooleanAccumulator a = BooleanAccumulator.treeGate(AND);
        for (IndexedEntry<BooleanValue> e0 : cells) {
            if (a.add(factory.or(e0.value().negation(), other.fastGet(e0.index()))) == FALSE)
                return FALSE;
        }
        BooleanValue val = factory.accumulate(a);
        return DefCond.ensureDef(factory, env, val, this.defCond(), other.defCond());
    }

    /**
     * Returns a formula stating that the entries in this matrix are equivalent to
     * the entries in the given matrix; i.e. the value of every entry in this matrix
     * is true if and only if the value of the corresponding entry in the given
     * matrix is true. The same formula can be obtained by calling
     * factory.and(this.subset(other), other.subset(this)), but this method performs
     * the operation more efficiently.
     *
     * @return { f: BooleanValue | f <=> (this.elements[0]<=>other.elements[0]) AND
     *         ... AND
     *         (this.elements[this.dimensions.capacity-1]<=>other.elements[this.dimensions.capacity-1]))
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanValue eq(BooleanMatrix other, Environment< ? , ? > env) {
        BooleanValue val = factory.and(this.subset(other, env), other.subset(this, env));
        return DefCond.ensureDef(factory, env, val, this.defCond(), other.defCond());
    }

    /**
     * Returns a matrix representing the asymmetric difference between the entries
     * in this and the given matrix. The same matrix can be obtained by calling
     * this.and(other.not()), but this method performs the operation more
     * efficiently (intermediate values are not explicity created).
     *
     * @return { m: BooleanMatrix | m.dimensions = this.dimensions && m.factory =
     *         this.factory && all i: [0..m.dimensions.capacity) | m.elements[i] =
     *         this.elements[i] AND !other.elements[i] }
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanMatrix difference(BooleanMatrix other) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);

        final BooleanMatrix ret = new BooleanMatrix(dims, factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        for (IndexedEntry<BooleanValue> e0 : cells) {
            ret.fastSet(e0.index(), factory.and(e0.value(), other.fastGet(e0.index()).negation()));
        }

        return ret;
    }

    /**
     * Returns the transitive closure of this matrix.
     *
     * @return { m: BooleanMatrix | m = ^this }
     * @throws UnsupportedOperationException #this.diensions != 2 ||
     *             !this.dimensions.square()
     */
    public final BooleanMatrix closure() {
        if (dims.numDimensions() != 2 || !dims.isSquare()) {
            throw new UnsupportedOperationException("#this.diensions != 2 || !this.dimensions.square()");
        }
        if (cells.isEmpty())
            return clone();

        // System.out.println("closure of " + this);
        BooleanMatrix ret = this;

        // compute the number of rows in the matrix
        int rowNum = 0;
        final int rowFactor = dims.dimension(1);
        for (IndexedEntry<BooleanValue> rowLead = cells.first(); rowLead != null; rowLead = cells.ceil(((rowLead.index() / rowFactor) + 1) * rowFactor)) {
            rowNum++;
        }

        // compute closure using iterative squaring
        for (int i = 1; i < rowNum; i *= 2) {
            ret = ret.or(ret.dot(ret));
        }
        // System.out.println(ret);
        return ret == this ? clone() : ret;
    }

    /**
     * Returns the transpose of this matrix.
     *
     * @return { m: BooleanMatrix | m = ~this }
     * @throws UnsupportedOperationException #this.dimensions != 2
     */
    public final BooleanMatrix transpose() {
        final BooleanMatrix ret = new BooleanMatrix(dims.transpose(), factory, cells, cells);
        ret.mergeDefConds(this);

        final int rows = dims.dimension(0), cols = dims.dimension(1);
        for (IndexedEntry<BooleanValue> e0 : cells) {
            ret.cells.put((e0.index() % cols) * rows + (e0.index() / cols), e0.value());
        }
        return ret;
    }

    /**
     * Returns a boolean matrix m such that m = this if the given condition
     * evaluates to TRUE and m = other otherwise.
     *
     * @return { m: BooleanMatrix | m.dimensions = this.dimensions && all i:
     *         [0..m.dimensions.capacity) | m.elements[i] = condition =>
     *         this.elements[i], other.elements[i] }
     * @throws NullPointerException other = null || condition = null
     * @throws IllegalArgumentException !other.dimensions.equals(this.dimensions) ||
     *             this.factory != other.factory
     */
    public final BooleanMatrix choice(BooleanValue condition, BooleanMatrix other) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);
        if (condition == TRUE)
            return this.clone();
        else if (condition == FALSE)
            return other.clone();

        final BooleanMatrix ret = new BooleanMatrix(dims, factory);
        final SparseSequence<BooleanValue> otherCells = other.cells;
        for (IndexedEntry<BooleanValue> e0 : cells) {
            BooleanValue v1 = otherCells.get(e0.index());
            if (v1 == null)
                ret.fastSet(e0.index(), factory.and(condition, e0.value()));
            else
                ret.fastSet(e0.index(), factory.ite(condition, e0.value(), v1));
        }
        for (IndexedEntry<BooleanValue> e1 : other.cells) {
            if (!cells.containsIndex(e1.index()))
                ret.fastSet(e1.index(), factory.and(condition.negation(), e1.value()));
        }

        BooleanValue of = factory.ite(condition, defCond().getOverflow(), other.defCond().getOverflow());
        BooleanValue accumOF = factory.ite(condition, defCond().getAccumOverflow(), other.defCond().getAccumOverflow());
        ret.defCond().setOverflows(of, accumOF);
        return ret;
    }

    /**
     * Returns a matrix m such that the relational value of m is equal to the
     * relational value of this projected on the specified columns.
     *
     * @requires column[int] in this.dimensions.dimensions[int]
     * @requires this.dimensions.isSquare()
     * @return { m: BooleanMatrix | [[m]] = project([[this]], columns) }
     * @throws IllegalArgumentExceptions columns.length < 1 ||
     *             !this.dimensions.isSquare()
     * @throws NullPointerException columns = null
     */
    public final BooleanMatrix project(Int[] columns) {
        if (!dims.isSquare())
            throw new IllegalArgumentException("!this.dimensions.isSquare()");

        final int rdnum = columns.length;

        if (rdnum < 1)
            throw new IllegalArgumentException("columns.length < 1");

        final Dimensions rdims = Dimensions.square(dims.dimension(0), rdnum);
        final BooleanMatrix ret = new BooleanMatrix(rdims, factory, cells, cells);
        ret.mergeDefConds(this);

        final int tdnum = dims.numDimensions();
        final int[] tvector = new int[tdnum];
        final int[] ivector = new int[rdnum];
        final int[] rvector = new int[rdnum];

        int nVarCols = 1;

        // detect constant columns to avoid unnecessary looping;
        for (int i = 0; i < rdnum; i++) {
            if (columns[i].isConstant()) {
                int value = columns[i].value();
                if (value < 0 || value >= tdnum) {
                    return ret;
                } else { // distinguish constants by making them negative
                    ivector[i] = -value;
                }
            } else {
                nVarCols *= tdnum;
            }
        }

        PROJECT: for (int i = 0; i < nVarCols; i++) {
            BooleanValue colVal = TRUE;
            for (int j = 0; j < rdnum; j++) {
                // if the jth column is non-constant, check that it can take on
                // the value ivector[j]
                if (ivector[j] >= 0) {
                    colVal = factory.and(colVal, columns[j].eq(factory.integer(ivector[j])));
                    if (colVal == FALSE)
                        continue PROJECT;
                }
            }
            for (IndexedEntry<BooleanValue> e : cells) {
                dims.convert(e.index(), tvector);
                for (int j = 0; j < rdnum; j++) {
                    rvector[j] = tvector[StrictMath.abs(ivector[j])];
                }
                int rindex = rdims.convert(rvector);
                ret.fastSet(rindex, factory.or(factory.and(e.value(), colVal), ret.fastGet(rindex)));
            }
            for (int j = rdnum - 1; j >= 0; j--) { // update ivector
                // update ivector[j] only if the jth column is not constant
                if (ivector[j] >= 0) {
                    if (ivector[j] + 1 == tdnum) {
                        ivector[j] = 0;
                    } else {
                        ivector[j] += 1;
                        break;
                    }
                }
            }
        }

        return ret;
    }

    /**
     * Returns a conjunction of the negated values between start, inclusive, and
     * end, exclusive.
     *
     * @requires 0 <= start < end <= this.dimensions.capacity()
     * @return !this.elements[start] && !this.elements[start+1] && ... &&
     *         !this.elements[end-1]
     */
    private final BooleanValue nand(int start, int end) {
        final BooleanAccumulator g = BooleanAccumulator.treeGate(AND);
        for (Iterator<IndexedEntry<BooleanValue>> iter = cells.iterator(start, end - 1); iter.hasNext();) {
            if (g.add(iter.next().value().negation()) == FALSE)
                return FALSE;
        }
        return factory.accumulate(g);
    }

    /**
     * Overrides the values in this matrix with those in <code>other</code>.
     * Specifically, for each index i of the returned matrix m, m.elements[i] is
     * true iff other.elements[i] is true or this.elements[i] is true and all
     * elements of <code>other</code> that are in the same row as i are false.
     *
     * @return {m: BooleanMatrix | m.dimensions = this.dimensions && all i:
     *         [0..m.capacity()) | m.elements[i] = other.elements[i] ||
     *         this.elements[i] && !OR(other.elements[row(i)]) } where
     *         other.elements[row(i)] selects all elements of <code>other</code>
     *         that are in the same row as i.
     * @throws NullPointerException other = null
     * @throws IllegalArgumentException other.dimensions != this.dimensions
     */
    public final BooleanMatrix override(BooleanMatrix other) {
        checkFactory(this.factory, other.factory);
        checkDimensions(this.dims, other.dims);
        if (other.cells.isEmpty())
            return this.clone();

        final BooleanMatrix ret = new BooleanMatrix(dims, factory, cells, other.cells);
        ret.mergeDefConds(this, other);

        ret.cells.putAll(other.cells);
        final int rowLength = dims.capacity() / dims.dimension(0);
        int row = -1;
        BooleanValue rowVal = BooleanConstant.TRUE;
        for (IndexedEntry<BooleanValue> e0 : cells) {
            int e0row = e0.index() / rowLength;
            if (row != e0row) {
                row = e0row;
                rowVal = other.nand(row * rowLength, (row + 1) * rowLength);
            }
            ret.fastSet(e0.index(), factory.or(ret.fastGet(e0.index()), factory.and(e0.value(), rowVal)));
        }
        return ret;
    }

    /**
     * Overrides the values in this matrix with those in <code>other</code>.
     *
     * @return others.length = 0 => { m: BooleanMatrix | m.dimensions =
     *         this.dimensions && m.elements = this.elements) else others.length = 1
     *         => {m: BooleanMatrix | m.dimensions = this.dimensions && all i:
     *         [0..m.capacity()) | m.elements[i] = other.elements[i] ||
     *         this.elements[i] && !OR(other.elements[rowOf(i)]) } else
     *         this.override(others[0).override(others[1..others.length))
     * @throws NullPointerException others = null
     * @throws IllegalArgumentException others[int].factory != this.factory or
     *             others[int].dimensions != this.dimensions
     */
    public final BooleanMatrix override(BooleanMatrix... others) {
        if (others.length == 0)
            return clone();
        final BooleanMatrix[] matrices = Containers.copy(others, 0, new BooleanMatrix[others.length + 1], 1, others.length);
        matrices[0] = this;
        for (int part = matrices.length; part > 1; part -= part / 2) {
            final int max = part - 1;
            for (int i = 0; i < max; i += 2) {
                matrices[i / 2] = matrices[i].override(matrices[i + 1]);
            }
            if (max % 2 == 0) { // even max => odd number of entries
                matrices[max / 2] = matrices[max];
            }
        }
        return matrices[0];
    }

    /**
     * Returns an Int that represents the cardinality (number of non-FALSE entries)
     * of this matrix using this.factory.intEncoding.
     *
     * @return {i: Int | [[i]] = sum({v: elements[int] | if [[v]] then 1 else 0}) }
     */
    public final Int cardinality() {
        final Int ret = factory.sum(cells.values());
        BooleanValue accum = DefCond.merge(factory, ret.defCond(), this.defCond());
        ret.defCond().setOverflows(ret.defCond().getOverflow(), accum);
        return ret;
    }

    /**
     * Returns a BooleanValue that constrains at least one value in this.elements to
     * be true. The effect of this method is the same as calling this.orFold().
     *
     * @return { f: BooleanValue | f <=> this.elements[0] || ... ||
     *         this.elements[this.dimensions.capacity-1] }
     */
    public final BooleanValue some(Environment< ? , ? > env) {
        final BooleanAccumulator g = BooleanAccumulator.treeGate(OR);
        for (IndexedEntry<BooleanValue> e : cells) {
            if (g.add(e.value()) == TRUE)
                return TRUE;
        }
        final BooleanValue val = factory.accumulate(g);
        return DefCond.ensureDef(factory, env, val, this.defCond());
    }

    /**
     * Returns a BooleanValue that constrains at most one value in this.elements to
     * be true. The effect of this method is the same as calling
     * this.factory.or(this.one(), this.none()).
     *
     * @return { f: BooleanValue | f <=> this.one() || this.none() }
     */
    public final BooleanValue lone(Environment< ? , ? > env) {
        if (cells.isEmpty())
            return TRUE;
        else {
            final BooleanAccumulator g = BooleanAccumulator.treeGate(AND);

            BooleanValue partial = FALSE;
            for (IndexedEntry<BooleanValue> e : cells) {
                if (g.add(factory.or(e.value().negation(), partial.negation())) == FALSE)
                    return FALSE;
                partial = factory.or(partial, e.value());
            }

            final BooleanValue val = factory.accumulate(g);
            return DefCond.ensureDef(factory, env, val, this.defCond());
        }
    }

    /**
     * Returns a BooleanValue that constraints exactly one value in this.elements to
     * be true.
     *
     * @return { f: BooleanValue | f <=> #this.elements[int] = 1 }
     */
    public final BooleanValue one(Environment< ? , ? > env) {
        if (cells.isEmpty())
            return FALSE;
        else {
            final BooleanAccumulator g = BooleanAccumulator.treeGate(AND);

            BooleanValue partial = FALSE;
            for (IndexedEntry<BooleanValue> e : cells) {
                if (g.add(factory.or(e.value().negation(), partial.negation())) == FALSE)
                    return FALSE;
                partial = factory.or(partial, e.value());
            }
            g.add(partial);

            final BooleanValue val = factory.accumulate(g);
            return DefCond.ensureDef(factory, env, val, this.defCond());
        }
    }

    /**
     * Returns a BooleanValue that constraints all values in this.elements to be
     * false. The effect of this method is the same as calling
     * this.factory.not(this.some()).
     *
     * @return { f: BooleanValue | f <=> !(this.elements[0] || ... ||
     *         !this.elements[this.dimensions.capacity-1]) }
     */
    public final BooleanValue none(Environment< ? , ? > env) {
        env.negate();
        BooleanValue val = some(env).negation();
        env.negate();
        return val;
    }

    /**
     * Sets the specified index to the given value.
     *
     * @requires value in this.factory.components
     * @ensures this.elements'[index] = value
     * @throws NullPointerException value = null
     * @throws IllegalArgumentException the given is a formula, and this matrix
     *             accepts only constants
     * @throws IndexOutOfBoundsException the given index does not belong to the set
     *             of indices at which this matrix can store non-FALSE values.
     */
    public final void set(final int index, final BooleanValue value) {
        if (!dims.validate(index))
            throw new IndexOutOfBoundsException("index < 0 || index >= this.dimensions.capacity");
        if (value == null)
            throw new NullPointerException("formula=null");
        if (value == FALSE)
            cells.remove(index);
        else
            cells.put(index, value);
    }

    /**
     * Returns a copy of this boolean matrix.
     *
     * @return {m: BooleanMatrix - this | m.dimensions = this.dimensions &&
     *         m.elements = copy of this.elements }
     */
    @Override
    public BooleanMatrix clone() {
        try {
            final BooleanMatrix ret = new BooleanMatrix(dims, factory, cells.clone());
            ret.mergeDefConds(this);
            return ret;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(); // unreachable code.
        }
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder buff = new StringBuilder("dimensions: ");
        buff.append(dims);
        buff.append(", elements: ");
        buff.append(cells);
        return buff.toString();
    }

}
