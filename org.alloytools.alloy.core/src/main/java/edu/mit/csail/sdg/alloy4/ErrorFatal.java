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

package edu.mit.csail.sdg.alloy4;

/** Immutable; this represents a fatal error. */

public final class ErrorFatal extends Err {

    /** This ensures this class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Constructs a new fatal error.
     *
     * @param msg - the actual error message (can be null)
     */
    public ErrorFatal(String msg) {
        super(null, msg, null);
    }

    /**
     * Constructs a new fatal error with "cause" as the underlying cause.
     *
     * @param msg - the actual error message (can be null)
     * @param cause - if nonnull, it is the cause of this exception
     */
    public ErrorFatal(String msg, Throwable cause) {
        super(null, msg, cause);
    }

    /**
     * Constructs a new fatal error.
     *
     * @param pos - the filename/line/row information (can be null if unknown)
     * @param msg - the actual error message (can be null)
     */
    public ErrorFatal(Pos pos, String msg) {
        super(pos, msg, null);
    }

    /** Returns a textual description of the error. */
    @Override
    public String toString() {
        if (pos == Pos.UNKNOWN)
            return "Fatal error:\n" + msg;
        if (pos.filename.length() > 0)
            return "Fatal error in " + pos.filename + " at line " + pos.y + " column " + pos.x + ":\n" + msg;
        return "Fatal error at line " + pos.y + " column " + pos.x + ":\n" + msg;
    }
}
