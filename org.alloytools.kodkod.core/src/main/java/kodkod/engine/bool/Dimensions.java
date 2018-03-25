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

import kodkod.engine.CapacityExceededException;
import kodkod.util.ints.Ints;

/**
 * Stores information about the size of a matrix. Specifically, for an
 * n-dimensional matrix n, a Dimensions object is abstractly a vector consisting
 * of n integers; the ith integer in the vector represents the size of the ith
 * dimension of a matrix.
 *
 * @specfield n: int
 * @specfield dimensions: [0..n) -> one int
 * @specfield capacity: dimensions[0] x ... x dimensions[n-1]
 * @invariant n > 0
 * @author Emina Torlak
 */
public abstract class Dimensions {

    private final int capacity;

    /**
     * Constructs a Dimensions with the given capacity.
     */
    private Dimensions(int capacity) {
        this.capacity = capacity;
    }

    /**
     * Returns a new Dimensions object with n dimensions, each of which has the
     * specified size.
     *
     * @return {d: Dimensions | d.n = n && d.dimensions[int] = size }
     * @throws IllegalArgumentException n < 1 || size < 1
     */
    public static Dimensions square(int size, int n) {
        if (n < 1 || size < 1)
            throw new IllegalArgumentException("n < 1 || size < 1");
        return new Square(n, size);
    }

    /**
     * Constructs a new Dimensions object with the given dimensions.
     *
     * @return {d: Dimensions | d.n = dimensions.length && d.dimensions = dimensions
     *         }
     * @throws NullPointerException dimensions = null
     * @throws IllegalArgumentException dimensions.length = 0 || some i:
     *             [0..dimensions.n) | dimensions[i] < 1
     */
    public static Dimensions rectangular(int[] dimensions) {
        if (dimensions.length == 0)
            throw new IllegalArgumentException("n=0.");
        long capacity = 1;
        int size = dimensions[0];
        for (int i = 0; i < dimensions.length; i++) {
            if (dimensions[i] < 1)
                throw new IllegalArgumentException("Invalid dimension: " + dimensions[i]);
            capacity *= dimensions[i];
            if (size != dimensions[i])
                size = 0;
        }
        if (size > 0) {
            return new Square(dimensions.length, size);
        } else {
            final int[] dims = new int[dimensions.length];
            System.arraycopy(dimensions, 0, dims, 0, dimensions.length);
            return new Rectangle(dims, capacity);
        }
    }

    /**
     * Returns the capacity of this.
     *
     * @return this.capacity
     */
    public final int capacity() {
        return capacity;
    }

    /**
     * Returns the size of the ith dimensions
     *
     * @return this.dimensions[i]
     * @throws ArrayIndexOutOfBoundsException i < 0 || i >= this.capacity
     */
    public abstract int dimension(int i);

    /**
     * Returns the number of dimensions in this Dimensions object.
     *
     * @return this.n
     */
    public abstract int numDimensions();

    /**
     * Returns true if this represents the dimensions of a square matrix; otherwise
     * returns false.
     *
     * @return all i, j: [0..capacity) | this.dimensions[i] = this.dimensions[j]
     */
    public abstract boolean isSquare();

    /**
     * Returns true if the dimensions data in this object is homogeneous from start,
     * inclusive, to end, exclusive.
     *
     * @return some x: int | this.dimensions[start..end) = x
     */
    abstract boolean isSquare(int start, int end);

    /**
     * Fills the destination array, beginning at destPos, with the dimension data
     * from this Dimensions object, beginning at srcPos. The number of components
     * copied is equal to the length argument. The dimensions at positions srcPos
     * through srcPos+length-1 are copied into positions destPos through
     * destPos+length-1, respectively, of the destination array.
     *
     * @ensures dest[destPos..destPos+length) =
     *          this.dimensions[srcPos..srcPos+length)
     */
    abstract void copy(int srcPos, int[] dest, int destPos, int length);

    /**
     * Returns the dimensions of a matrix that would result from multiplying a
     * matrix of dimensions given by this by a matrix whose dimensions are specified
     * by dim.
     *
     * @return { d: Dimensions | d.n = this.n + dim.n - 2 && (all i: [0..this.n-1) |
     *         d.dimensions[i] = this.dimensions[i]) && (all i: [this.n-1..d.n) |
     *         d.dimensions[i] = dim.dimensions[i-this.n+1])}
     * @throws IllegalArgumentException this.n + dim.n < 3 || this.dimensions[n-1]
     *             != dim.dimensions[0]
     */
    public final Dimensions dot(Dimensions dim) {
        final int n0 = numDimensions(), n1 = dim.numDimensions();
        final int n = n0 + n1 - 2, drop = dim.dimension(0);
        if (n == 0 || dimension(n0 - 1) != drop) {
            throw new IllegalArgumentException();
        }

        if (isSquare(0, n0 - 1) && dim.isSquare(1, n1) && (n0 == 1 || n1 == 1 || dimension(0) == dim.dimension(1))) {
            return new Square(n, dimension(0));
        } else {
            final int[] dims = new int[n];
            copy(0, dims, 0, n0 - 1);
            dim.copy(1, dims, n0 - 1, n1 - 1);
            return new Rectangle(dims, (capacity * dim.capacity) / (drop * drop));
        }
    }

    /**
     * Returns the dimensions of a matrix that would result from taking the cross
     * product of a matrix of dimensions given by this and a matrix whose dimensions
     * are specified by dim.
     *
     * @return { d: Dimensions | d.n = this.n + dim.n && (all i: [0..this.n) |
     *         d.dimensions[i] = this.dimensions[i]) && (all i: [this.n..d.n) |
     *         d.dimensions[i] = dim.dimensions[i-this.n])}
     */
    public final Dimensions cross(Dimensions dim) {
        final int n0 = numDimensions(), n1 = dim.numDimensions();
        if (isSquare() && dim.isSquare() && dimension(0) == dim.dimension(0))
            return new Square(n0 + n1, dimension(0));
        else {
            final int[] dims = new int[n0 + n1];
            copy(0, dims, 0, n0);
            dim.copy(0, dims, n0, n1);
            return new Rectangle(dims, (long) capacity * (long) dim.capacity);
        }
    }

    /**
     * Returns the transpose of these dimensions.
     *
     * @return { d: Dimensions | d.n = 2 && d.dimensions[0] = this.dimensions[1] &&
     *         d.dimensions[1] = this.dimensions[0] }
     * @throws UnsupportedOperationException this.n != 2
     */
    public abstract Dimensions transpose();

    /**
     * @return true if index is positive and less than bound.
     */
    private static boolean positiveBounded(int index, int bound) {
        return 0 <= index && index < bound;
    }

    /**
     * Returns true if index is a valid flat index for a matrix with these
     * dimensions; otherwise returns false.
     *
     * @return 0 <= i < this.capacity
     */
    public final boolean validate(int index) {
        return positiveBounded(index, capacity);
    }

    /**
     * Returns true if index is a valid vector index for a matrix with these
     * dimensions; otherwise returns false.
     *
     * @return index.length = n && (all i: [0..this.capacity) | 0 <= index[i] <
     *         this.dimensions[i])
     * @throws NullPointerException index = null
     */
    public final boolean validate(int[] index) {
        final int length = numDimensions();
        if (index.length != length)
            return false;
        for (int i = 0; i < length; i++) {
            if (!positiveBounded(index[i], dimension(i)))
                return false;
        }
        return true;
    }

    /**
     * Converts an integer index into a matrix with these dimensions into a vector
     * index. The effect of this method is the same as calling this.convert(index,
     * new int[this.numDimensions()]).
     *
     * @return an array of ints that represents a vector index corresponding to the
     *         specified integer index into a
     *         this.dimensions[0]x...xthis.dimensions[n-1] matrix
     * @throws IndexOutOfBoundsException !validate(index)
     */
    public final int[] convert(int index) {
        final int[] vector = new int[numDimensions()];
        convert(index, vector);
        return vector;
    }

    /**
     * Converts an integer index into a matrix with these dimensions into a vector
     * index, and stores the result in the provided array. This method requires that
     * the array argument have at least this.n cells, which are used to store the
     * vector representation of the given index. The contents of the cells of
     * <code>vectorIndex</code> beyond the first this.n cells are left unchanged.
     *
     * @requires vectorIndex.length <= this.n
     * @ensures the first this.numDimensions entries of <code>vectorIndex</code>
     *          contain the vector index representation of the specified integer
     *          index into a this.dimensions[0]x...xthis.dimensions[n-1] matrix
     * @throws NullPointerException vectorIndex = null
     * @throws IllegalArgumentException vectorIndex.length < this.numDimensions
     * @throws IndexOutOfBoundsException !validate(index)
     */
    public final void convert(int index, int[] vectorIndex) {
        final int length = numDimensions();
        if (vectorIndex.length < length)
            throw new IllegalArgumentException("arrayIndex.length<this.numDimensions");
        if (!validate(index))
            throw new IndexOutOfBoundsException("index");
        int conversionFactor = capacity;
        int remainder = index;
        for (int i = 0; i < length; i++) {
            conversionFactor = conversionFactor / dimension(i);
            vectorIndex[i] = remainder / conversionFactor;
            remainder = remainder % conversionFactor;
        }
    }

    /**
     * Converts the first this.n positions of the given vector index into an integer
     * index.
     *
     * @return an integer index corresponding to the first this.numDimensions
     *         positions of the specified vector index into a
     *         this.dimensions[0]x...xthis.dimensions[n-1] matrix
     * @throws NullPointerException index == null
     * @throws IllegalArgumentException index.length < this.n
     * @throws IndexOutOfBoundsException some i: [0..n) | index[i] < 0 || index[i]
     *             >= this.dimensions[i]
     */
    public final int convert(int[] vectorIndex) {
        final int length = numDimensions();
        if (vectorIndex.length < length) {
            throw new IllegalArgumentException("index.length < this.n");
        }
        int intIndex = 0;
        int conversionFactor = capacity;
        for (int i = 0; i < length; i++) {
            int dim = dimension(i);
            if (!positiveBounded(vectorIndex[i], dim))
                throw new IndexOutOfBoundsException("index[" + i + "]");
            conversionFactor = conversionFactor / dim;
            intIndex += conversionFactor * vectorIndex[i];
        }
        return intIndex;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder buffer = new StringBuilder("[ ");
        for (int i = 0; i < numDimensions(); i++) {
            buffer.append(dimension(i));
            buffer.append(" ");
        }
        buffer.append("]");
        return buffer.toString();
    }

    /**
     * Represents a Dimensions object whose dimensions are all of the same size.
     */
    private static final class Square extends Dimensions {

        private final int n, size;

        /**
         * Constructs a new Dimensions object with n dimensions, each of which has the
         * specified size.
         *
         * @ensures this.n' = n && this.dimensions[int] = size
         * @requires size > 0 && n > 0
         * @throws IllegalArgumentException n < 1 || size < 1
         */
        Square(int n, int size) {
            super(capacity(n, size));
            this.size = size;
            this.n = n;
        }

        static int capacity(int n, int size) {
            final long cap = Math.round(Math.pow(size, n));
            if (cap > Integer.MAX_VALUE || cap <= 0)
                throw new CapacityExceededException("Matrix too large: requested capacity of " + cap, Ints.nCopies(n, size));
            return (int) cap;
        }

        @Override
        void copy(int srcPos, int[] dest, int destPos, int length) {
            if (srcPos < 0 || length < 0 || srcPos + length > n)
                throw new ArrayIndexOutOfBoundsException();
            while (srcPos++ < length) {
                dest[destPos++] = size;
            }
        }

        @Override
        boolean isSquare(int start, int end) {
            if (start <= end && start >= 0 && end <= n) {
                return true;
            }
            throw new ArrayIndexOutOfBoundsException();
        }

        @Override
        public int numDimensions() {
            return n;
        }

        @Override
        public int dimension(int i) {
            if (!positiveBounded(i, n))
                throw new ArrayIndexOutOfBoundsException();
            return size;
        }

        @Override
        public boolean isSquare() {
            return true;
        }

        @Override
        public Dimensions transpose() {
            if (numDimensions() != 2)
                throw new UnsupportedOperationException("n!=2");
            return this;
        }

        /**
         * Returns true if the given object is logically equivalent to this; otherwise
         * returns false.
         *
         * @return this.dimensions = o.dimensions
         */
        @Override
        public boolean equals(Object o) {
            if (o instanceof Square) {
                final Square s = (Square) o;
                return n == s.n && size == s.size;
            }
            return false;
        }

        @Override
        public int hashCode() {
            return n ^ size;
        }

    }

    /**
     * Represents a Dimensions object with at least two dimensions of different
     * size.
     */
    private static final class Rectangle extends Dimensions {

        private final int[] dimensions;

        /**
         * Constructs a new Dimensions object with the given dimensions.
         *
         * @ensures this.n' = dimensions.length && this.dimensions' = dimensions
         * @requires - dimensions.length > 0 && (all i: [0..dimensions.n) |
         *           dimensions[i] > 0) && (some i, j: [0..dimensions.n) | dimensions[i]
         *           != dimensions[j]) && capacity =
         *           dimensions[0]*dimensions[1]*...*dimensions[dimensions.length-1]
         */
        Rectangle(int[] dims, long capacity) {
            super((int) capacity);
            if (capacity > Integer.MAX_VALUE || capacity <= 0)
                throw new CapacityExceededException("Matrix too large: requested capacity of " + capacity, Ints.asIntVector(dims));
            this.dimensions = dims;
        }

        @Override
        void copy(int srcPos, int[] dest, int destPos, int length) {
            System.arraycopy(dimensions, srcPos, dest, destPos, length);
        }

        @Override
        boolean isSquare(int start, int end) {
            for (int i = start + 1; i < end; i++) {
                if (dimensions[i - 1] != dimensions[i])
                    return false;
            }
            return true;
        }

        @Override
        public boolean isSquare() {
            return false;
        }

        @Override
        public int dimension(int i) {
            return dimensions[i];
        }

        @Override
        public int numDimensions() {
            return dimensions.length;
        }

        @Override
        public Dimensions transpose() {
            if (numDimensions() != 2)
                throw new UnsupportedOperationException("n!=2");
            int[] dims = {
                          dimensions[1], dimensions[0]
            };
            return new Rectangle(dims, capacity());
        }

        /**
         * Returns true if the given object is logically equivalent to this; otherwise
         * returns false.
         *
         * @return this.dimensions = dim.dimensions
         */
        @Override
        public boolean equals(Object o) {
            if (o instanceof Rectangle) {
                final Rectangle r = (Rectangle) o;
                if (dimensions.length != r.dimensions.length || capacity() != r.capacity())
                    return false;
                for (int i = 0; i < dimensions.length; i++) {
                    if (dimensions[i] != r.dimensions[i])
                        return false;
                }
                return true;
            }
            return false;

        }

        @Override
        public int hashCode() {
            return dimensions.length ^ capacity();
        }

    }

}
