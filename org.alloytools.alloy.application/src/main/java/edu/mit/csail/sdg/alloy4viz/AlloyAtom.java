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

package edu.mit.csail.sdg.alloy4viz;

/**
 * Immutable; represents an Alloy atom in an instance.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyAtom implements Comparable<AlloyAtom> {

    /**
     * The original name of this atom from the original Kodkod or other analysis.
     */
    private final String    originalName;

    /**
     * The most specific AlloyType that this atom belongs to.
     */
    private final AlloyType type;

    /**
     * The index is a number that differentiates atoms of the same AlloyType; one
     * special convention: (this atom is the only atom with this type) iff
     * (index==Integer.MAX_VALUE)
     */
    private final int       index;

    /** Create a new AlloyAtom with the given type and index. */
    public AlloyAtom(AlloyType type, int index) {
        this.type = type;
        this.index = index;
        this.originalName = type.getName() + "." + index;
    }

    /**
     * Create a new AlloyAtom with the given type, index, and label.
     */
    public AlloyAtom(AlloyType type, int index, String originalName) {
        this.type = type;
        this.index = index;
        this.originalName = originalName;
    }

    /**
     * Return a label for this atom as recommended by a theme (theme can be null if
     * there's no theme to consult).
     */
    public String getVizName(VizState theme, boolean numberAtoms) {
        if (theme != null) {
            if (theme.useOriginalName() || type.getName().equals("String"))
                return originalName;
            if (index == Integer.MAX_VALUE && type.getName().equals("Int") && theme.label.get(type).length() == 0) {
                // Special handling for Meta Model. (Only meta model could have
                // index==MAX_VALUE)
                return "Int";
            }
            if (index == Integer.MIN_VALUE && type.getName().equals("seq/Int") && theme.label.get(type).length() == 0) {
                // Special handling for Meta Model. (Only meta model could have
                // index==MIN_VALUE)
                return "seq/Int";
            }
            if (index == Integer.MAX_VALUE || !numberAtoms)
                return theme.label.get(type);
            else
                return theme.label.get(type) + index;
        }
        if (type.getName().equals("Int"))
            return "" + index; // Special override to display integers better
        if (type.getName().equals("seq/Int"))
            return "" + index; // Special override to display integers better
        if (index == Integer.MAX_VALUE || !numberAtoms)
            return type.getName();
        else
            return type.getName() + index;
    }

    /** Return the type of the AlloyAtom. */
    public AlloyType getType() {
        return type;
    }

    /**
     * Provides a human-readable label for debugging purpose.
     */
    @Override
    public String toString() {
        return getVizName(null, true);
    }

    /**
     * Compare first by type, then by index, then by the original names. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     * <p>
     * As a special cosmetic enhancement: if we're comparing integer atoms, we want
     * to ignore the difference between seqInt and Int.
     */
    @Override
    public int compareTo(AlloyAtom otherAtom) {
        if (otherAtom == null)
            return 1;
        AlloyType at = type;
        if (at.equals(AlloyType.SEQINT))
            at = AlloyType.INT;
        AlloyType bt = otherAtom.type;
        if (bt.equals(AlloyType.SEQINT))
            bt = AlloyType.INT;
        // This renaming is necessary in order to make sure the comparison is
        // transitive.
        // For example, assuming seq/Int comprises 0..3, then we want atom0 <
        // atom5,
        // even though atom0's TYPENAME > atom5's TYPENAME.
        // On the other hand, if you have an atom X with type X, then we want to
        // make sure X>5 just like X>0
        // (even though lexically, the type name "X" < the type name "seq/Int"
        if (at.equals(AlloyType.INT) && bt.equals(AlloyType.INT))
            return (index < otherAtom.index) ? -1 : ((index > otherAtom.index) ? 1 : 0);
        int result = at.compareTo(bt);
        if (result != 0)
            return result;
        // We don't want to use the "return (index-otherAtom.index);" trick,
        // especially since singleton sets will have index of Integer.MAX_VALUE.
        if (index != otherAtom.index)
            return (index < otherAtom.index) ? -1 : 1;
        return originalName.compareTo(otherAtom.originalName);
    }

    /**
     * Two AlloyAtoms are equal if they have the same type, same index, and same
     * original name.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyAtom))
            return false;
        if (other == this)
            return true;
        AlloyAtom otherAtom = (AlloyAtom) other;
        return index == otherAtom.index && type.equals(otherAtom.type) && originalName.equals(otherAtom.originalName);
    }

    /** Returns a hash code based on the type and index. */
    @Override
    public int hashCode() {
        return 7 * type.hashCode() + 5 * index + 17 * originalName.hashCode();
    }
}
