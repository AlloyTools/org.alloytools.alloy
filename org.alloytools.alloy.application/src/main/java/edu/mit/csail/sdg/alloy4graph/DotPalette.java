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

/**
 * Immutable; this defines the set of possible color palettes.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public enum DotPalette {

                        // Note: if you change the order, you must also change the ordering of the
                        // colors in DotColor class.
                        /** Classic palette. */
                        CLASSIC("Classic"),
                        /** Standard palette. */
                        STANDARD("Standard"),
                        /** Martha palette. */
                        MARTHA("Martha"),
                        /** Neon palette. */
                        NEON("Neon");

    /** The text to display. */
    private final String displayText;

    /** Constructs a DotPalette object with the given label. */
    private DotPalette(String displayText) {
        this.displayText = displayText;
    }

    /**
     * This method is used in parsing the XML value into a valid DotPalette; returns
     * null if there is no match.
     */
    public static DotPalette parse(String x) {
        if (x != null)
            for (DotPalette d : values())
                if (d.toString().equals(x))
                    return d;
        return null;
    }

    /**
     * Returns the String that will be displayed in the GUI to represent this value.
     */
    public String getDisplayedText() {
        return displayText;
    }

    /** This value is used in writing XML. */
    @Override
    public String toString() {
        return displayText;
    }
}
