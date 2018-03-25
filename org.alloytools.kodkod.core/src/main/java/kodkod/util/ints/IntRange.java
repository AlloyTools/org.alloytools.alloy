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
package kodkod.util.ints;

/**
 * Represents a range of integers, [min..max].
 *
 * @specfield min: int
 * @specfield max: int
 * @invariant min <= max
 * @author Emina Torlak
 */
public abstract class IntRange {

    private IntRange() {}

    /**
     * Returns the left endpoint of this range.
     *
     * @return this.min
     */
    public abstract int min();

    /**
     * Returns the right endpoint of this range.
     *
     * @return this.max
     */
    public abstract int max();

    /**
     * Returns the number of element in this range.
     *
     * @return this.max - this.min + 1
     */
    public int size() {
        return max() - min() + 1;
    }

    /**
     * Returns true if the given integer is within this range; otherwise returns
     * false.
     *
     * @return i in [min..max]
     */
    public boolean contains(int i) {
        return i >= min() && i <= max();
    }

    /**
     * Returns true if this range contains the given range.
     *
     * @return this.min <= range.min <= range.max <= this.max
     * @throws NullPointerException range = null
     */
    public boolean contains(IntRange range) {
        return min() <= range.min() && range.max() <= max();
    }

    /**
     * Returns true if this and the given range intersect.
     *
     * @return some i: int | this.contains(i) && range.contains(i)
     * @throws NullPointerException range = null
     */
    public boolean intersects(IntRange range) {
        return contains(range.min()) || contains(range.max());
    }

    /**
     * Returns true if o is an int range with the same endpoints as this.
     *
     * @return o in IntRange && o.min==this.min && o.max==this.max
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof IntRange) {
            final IntRange r = (IntRange) o;
            return min() == r.min() && max() == r.max();
        }
        return false;
    }

    /**
     * Returns the hash code for this int range. The implementation is guaranteed to
     * obey the Object contract.
     *
     * @return the hashcode for this intrange
     */
    @Override
    public int hashCode() {
        return min() == max() ? min() : min() ^ max();
    }

    @Override
    public String toString() {
        return "[" + min() + ".." + max() + "]";
    }

    /**
     * Represents an int range that consists of a single point.
     *
     * @invariant min==max
     * @author Emina Torlak
     */
    static final class OnePointRange extends IntRange {

        private final int min;

        /**
         * Constructs a new one point range.
         */
        OnePointRange(int min) {
            this.min = min;
        }

        @Override
        public final int min() {
            return min;
        }

        @Override
        public final int max() {
            return min;
        }
    }

    /**
     * Represents an int range with two distinct end points.
     *
     * @invariant min < max
     * @author Emina Torlak
     */
    static final class TwoPointRange extends IntRange {

        private final int min, max;

        /**
         * Constructs a new two point range.
         *
         * @requires min < max
         */
        TwoPointRange(int min, int max) {
            assert min < max;
            this.min = min;
            this.max = max;
        }

        @Override
        public final int min() {
            return min;
        }

        @Override
        public final int max() {
            return max;
        }
    }

}
