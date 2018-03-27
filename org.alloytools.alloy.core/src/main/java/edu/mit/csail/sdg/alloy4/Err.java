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

/**
 * Immutable; this is the abstract parent class of the various possible errors.
 */

public abstract class Err extends RuntimeException {

    /** This ensures this class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * This stores the filename/line/column information (Pos.UNKNOWN if unknown)
     * (never null)
     */
    public final Pos          pos;

    /** The actual error message (never null) */
    public final String       msg;

    /**
     * Constructs a new Err object.
     *
     * @param pos - the filename/line/row information (can be null if unknown)
     * @param msg - the actual error message (can be null)
     * @param cause - if nonnull, it will be recorded as the cause of this exception
     */
    Err(Pos pos, String msg, Throwable cause) {
        super((msg == null ? "" : msg), cause);
        this.pos = (pos == null ? Pos.UNKNOWN : pos);
        this.msg = (msg == null ? "" : msg);
    }

    /**
     * Two Err objects are equal if the type, position, and message are the same.
     */
    @Override
    public final boolean equals(Object other) {
        if (this == other)
            return true;
        else if (other == null || getClass() != other.getClass())
            return false;
        Err that = (Err) other;
        return pos.equals(that.pos) && msg.equals(that.msg);
    }

    /** Returns a hash code consistent with equals() */
    @Override
    public final int hashCode() {
        return msg.hashCode();
    }

    /**
     * Returns this exception type, its error message, and its complete stack trace
     * as a String.
     */
    public final String dump() {
        return MailBug.dump(this);
    }
}
