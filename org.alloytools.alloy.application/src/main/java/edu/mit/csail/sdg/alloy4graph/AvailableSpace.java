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

package edu.mit.csail.sdg.alloy4graph;

import java.util.ArrayList;
import java.util.List;

/**
 * Mutable; this allows you to compute whether a rectangle overlaps with a set
 * of rectangles or not.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AvailableSpace {

    /** Mutable; represents a rectangle. */
    static final class Box {

        /** (x,y) is the top-left corner. */
        int       x, y;
        /** (w,h) is the width and height. */
        final int w, h;

        public Box(int x, int y, int w, int h) {
            this.x = x;
            this.y = y;
            this.w = w;
            this.h = h;
        }
    }

    /**
     * The list of existing rectangles; we ensure every rectangle in here has
     * width>0 and height>0.
     */
    private List<Box> list = new ArrayList<Box>();

    /** Construct an empty space. */
    public AvailableSpace() {}

    /**
     * Returns true if the given rectangle does not overlap with any existing
     * rectangle in this space.
     */
    public boolean ok(int x, int y, int w, int h) {
        if (w <= 0 || h <= 0)
            return true; // always okay
        for (Box box : list) {
            if ((x >= box.x && x <= box.x + box.w - 1) || (x + w >= box.x + 1 && x + w <= box.x + box.w))
                if ((y >= box.y && y <= box.y + box.h - 1) || (y + h >= box.y + 1 && y + h <= box.y + box.h))
                    return false;
            if ((box.x >= x && box.x <= x + w - 1) || (box.x + box.w >= x + 1 && box.x + box.w <= x + w))
                if ((box.y >= y && box.y <= y + h - 1) || (box.y + box.h >= y + 1 && box.y + box.h <= y + h))
                    return false;
        }
        return true;
    }

    /**
     * Add the given rectangle to the list of rectangles in this space.
     */
    public void add(int x, int y, int w, int h) {
        if (w <= 0 || h <= 0)
            return; // no-op
        list.add(new Box(x, y, w, h));
    }

    /** Erases the list of rectangles in this space. */
    public void clear() {
        list.clear();
    }
}
