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

import javax.swing.Icon;

import edu.mit.csail.sdg.alloy4.OurUtil;

/**
 * Immutable; this defines the set of possible line styles (SOLID, DASHED,
 * DOTTED...)
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public enum DotStyle {

                      /** Solid line. */
                      SOLID("Solid", "solid"),

                      /** Dashed line. */
                      DASHED("Dashed", "dashed"),

                      /** Dotted line. */
                      DOTTED("Dotted", "dotted"),

                      /** Bold line. */
                      BOLD("Bold", "bold");

    /** The description of this line style. */
    private final String name;

    /** The icon for this line style. */
    private final Icon   icon;

    /** The corresponding DOT attribute. */
    private final String dotName;

    /** Constructs a DotStyle object. */
    private DotStyle(String name, String dotName) {
        this.name = name;
        this.icon = OurUtil.loadIcon("icons/StyleIcons/" + dotName + ".gif");
        this.dotName = dotName;
    }

    /**
     * Returns the String that will be displayed in the GUI to represent this value.
     */
    public String getDisplayedText() {
        return name;
    }

    /**
     * Returns the String that should be written into the dot file for this value,
     * when used with the given palette.
     */
    public String getDotText() {
        return dotName;
    }

    /**
     * Returns the Icon that will be displayed in the GUI to represent this value,
     * when used with the given palette.
     */
    public Icon getIcon() {
        return icon;
    }

    /**
     * This method is used in parsing the XML value into a valid style; returns null
     * if there is no match.
     */
    public static DotStyle parse(String x) {
        if (x != null)
            for (DotStyle d : values())
                if (d.name.equals(x))
                    return d;
        return null;
    }

    /** This value is used in writing XML. */
    @Override
    public String toString() {
        return name;
    }
}
