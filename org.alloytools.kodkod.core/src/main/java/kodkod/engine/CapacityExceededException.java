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
package kodkod.engine;

import kodkod.util.ints.IntVector;

/**
 * Indicates that a problem construction or translation task failed because the
 * capacity of the index representation was exceeded.
 *
 * @specfield dims: IntVector // contains a vector of dimensions which exceed
 *            the representation capacity
 * @author Emina Torlak
 */
public final class CapacityExceededException extends RuntimeException {

    private static final long serialVersionUID = -8098615204149641969L;
    private final IntVector   dims;

    /**
     * Constructs a CapacityExceededException from the given dimensions.
     */
    public CapacityExceededException(IntVector dims) {
        this.dims = dims;
    }

    /**
     * Constructs a CapacityExceededException with the given message and dimensions.
     */
    public CapacityExceededException(String arg0, IntVector dims) {
        super(arg0);
        this.dims = dims;
    }

    /**
     * Constructs a CapacityExceededException with the given cause.
     */
    public CapacityExceededException(Throwable arg0, IntVector dims) {
        super(arg0);
        this.dims = dims;
    }

    /**
     * Constructs a CapacityExceededException with the given message and cause.
     */
    public CapacityExceededException(String arg0, Throwable arg1, IntVector dims) {
        super(arg0, arg1);
        this.dims = dims;
    }

    /**
     * Returns the vector of dimensions which, when multiplied together, exceed the
     * representation capacity.
     *
     * @return this.dims
     */
    public final IntVector dims() {
        return dims;
    }

}
