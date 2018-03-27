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

import java.io.Serializable;

/**
 * Immutable; stores the filename and line/column position.
 * <p>
 * <b>Invariant:</b> filename!=null && x>0 && y>0 && ((y2>y && x2>0) || (y2==y
 * && x2>=x))
 * <p>
 * <b>Thread Safety:</b> Safe (since objects of this class are immutable).
 * <p>
 * The secondary position is part of the span. I.e. it points to the last
 * position in the stream that is spanned by this position. I.e. it the x2/y2
 * pair is inclusive
 */

public final class Pos implements Serializable {

    /** To make sure the serialization form is stable. */
    private static final long serialVersionUID = 0;

    /** The filename (it can be an empty string if unknown) */
    public final String       filename;

    /** The starting column position (from 1..) */
    public final int          x;

    /** The starting row position (from 1..) */
    public final int          y;

    /** The ending column position (from 1..) */
    public final int          x2;

    /** The ending row position (from 1..) */
    public final int          y2;

    /** The default "unknown" location. */
    public static final Pos   UNKNOWN          = new Pos("", 1, 1);

    /**
     * Constructs a new Pos object.
     *
     * @param filename - the filename (it can be an empty string if unknown)
     * @param x - the column position (from 1..)
     * @param y - the row position (from 1..)
     */
    public Pos(String filename, int x, int y) {
        this.filename = (filename == null ? "" : filename);
        this.x = (x > 0 ? x : 1);
        this.y = (y > 0 ? y : 1);
        this.x2 = this.x;
        this.y2 = this.y;
        assert y <= y2 && (y == y2 ? x <= x2 : true);
    }

    /**
     * Constructs a new Pos object.
     *
     * @param filename - the filename (it can be an empty string if unknown)
     * @param x - the starting column position (from 1..)
     * @param y - the starting row position (from 1..)
     * @param x2 - the ending column position (from 1..)
     * @param y2 - the ending row position (from 1..)
     */
    public Pos(String filename, int x, int y, int x2, int y2) {
        this.filename = (filename == null ? "" : filename);
        this.x = (x > 0 ? x : 1);
        this.y = (y > 0 ? y : 1);
        if (y2 < (this.y))
            y2 = this.y;
        if (y2 == this.y) {
            if (x2 < (this.x))
                x2 = this.x;
        } else {
            if (x2 < 1)
                x2 = 1;
        }
        this.x2 = x2;
        this.y2 = y2;
    }

    /**
     * Return a new position that merges this and that (it is assumed that the two
     * Pos objects have same filename)
     *
     * @param that - the other position object
     */
    public Pos merge(Pos that) {
        if (that == null || that == UNKNOWN || that == this)
            return this;
        if (this == UNKNOWN)
            return that;
        int x = this.x, y = this.y, x2 = that.x2, y2 = that.y2;
        if (that.y < y || (that.y == y && that.x < x)) {
            x = that.x;
            y = that.y;
        }
        if (this.y2 > y2 || (this.y2 == y2 && this.x2 > x2)) {
            x2 = this.x2;
            y2 = this.y2;
        }
        if (x == this.x && y == this.y && x2 == this.x2 && y2 == this.y2)
            return this; // avoid creating unnecessary new object
        if (x == that.x && y == that.y && x2 == that.x2 && y2 == that.y2)
            return that; // avoid creating unnecessary new object
        return new Pos(filename, x, y, x2, y2);
    }

    /**
     * Returns true if neither argument is null nor UNKNOWN, and that the ending
     * position of "a" is before the starting position of "b".
     */
    public static boolean before(Pos a, Pos b) {
        if (a == null || a == Pos.UNKNOWN || b == null || b == Pos.UNKNOWN || !a.filename.equals(b.filename))
            return false;
        return a.y2 < b.y || (a.y2 == b.y && a.x2 < b.x);
    }

    /**
     * Two Pos objects are equal if the filename x y x2 y2 are the same.
     */
    @Override
    public boolean equals(Object other) {
        if (this == other)
            return true;
        if (!(other instanceof Pos))
            return false;
        Pos that = (Pos) other;
        return x == that.x && y == that.y && x2 == that.x2 && y2 == that.y2 && filename.equals(that.filename);
    }

    /** Returns a hash code consistent with equals() */
    @Override
    public int hashCode() {
        return x * 111 + y * 171 + x2 * 1731 + y2 * 2117;
    }

    /**
     * Returns a short String representation of this position value.
     */
    public String toShortString() {
        String f = filename;
        int a = f.lastIndexOf('/'), b = f.lastIndexOf('\\');
        if (a < b)
            a = b;
        if (a >= 0)
            f = f.substring(a + 1);
        if (f.length() == 0)
            return "line " + y + ", column " + x;
        else
            return "line " + y + ", column " + x + ", filename=" + f;
    }

    /**
     * Returns a String representation of this position value.
     */
    @Override
    public String toString() {
        if (filename.length() == 0)
            return "line " + y + ", column " + x;
        else
            return "line " + y + ", column " + x + ", filename=" + filename;
    }

    int start() {
        return y * 500 + x;
    }

    int end() {
        return y2 * 500 + x2;
    }

    /*
     * Check if the given pos is contained in us. We assume that when the start of
     * the given pos is in our span then it completely is inside our span.
     */
    public boolean contains(Pos pos) {
        int anchor = pos.start();
        int ourStart = start();
        int ourEnd = end();
        if (ourStart > anchor)
            return false;

        if (ourEnd < anchor)
            return false;

        return true;
    }

    /*
     * Return a measure of wideness for this pos. This can be used to sort
     * overlapping pos's. The smallest wideness is the smallest span.
     */
    public int width() {
        return end() - start();
    }

    /*
     * Convert a start/end position to a Pos
     */
    public static Pos toPos(String text, int start, int end) {
        if (end > text.length() || end == -1)
            end = text.length();

        if (start < 0 || start >= end || end < 0 || end > text.length())
            return null;

        int row = 1, col = 1;
        int n = 0;
        while (n < start) {
            if (text.charAt(n) == '\n') {
                col = 1;
                row++;
            } else
                col++;
            n++;
        }

        int row2 = row, col2 = col - 1;

        while (n < end) {
            if (text.charAt(n) == '\n') {
                col2 = 1;
                row2++;
            } else
                col2++;
            n++;
        }
        return new Pos("", col, row, col2, row2);

    }

    /*
     * Calculate the range [start,end) for this position based on the given text.
     * Return null if this pos's span is outside the text. If the end of the span is
     * outside the length, cap it at the length.
     */

    public int[] toStartEnd(String text) {
        if (this == UNKNOWN)
            return null;

        int index = 0;
        int row = this.y - 1;
        int col = this.x - 1;

        while (index < text.length() && row > 0) {
            row--;
            index = text.indexOf('\n', index);
            if (index < 0)
                return null;
            index++;
        }

        index = index + col;
        if (index > text.length())
            return null;

        int start = index;
        row = y2 - y;
        col = y == y2 ? x2 - x + 1 : x2;

        while (index < text.length() && row > 0) {
            row--;
            index = text.indexOf('\n', index);
            if (index < 0) {
                return new int[] {
                                  start, text.length()
                };
            }
            index++;
        }
        index = index + col;
        if (index > text.length())
            index = text.length();

        int end = index;
        return new int[] {
                          start, end
        };
    }

    public String substring(String text) {
        int[] select = toStartEnd(text);
        if (select == null)
            return null;

        return text.substring(select[0], select[1]);

    }

    public boolean sameFile(Pos pos) {
        return this.filename.equals(pos.filename);
    }
}
