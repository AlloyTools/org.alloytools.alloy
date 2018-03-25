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

import edu.mit.csail.sdg.alloy4.Util;

/**
 * Immutable; represents an Alloy set in an instance.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloySet extends AlloyNodeElement {

    /** The parent type of this AlloySet. */
    private final AlloyType type;

    /**
     * Records whether this relation is known to be "private"; NOTE: this value is
     * NOT USED during equals() comparison.
     */
    public final boolean    isPrivate;

    /**
     * Records whether this relation is known to be "meta"; NOTE: this value is NOT
     * USED during equals() comparison.
     */
    public final boolean    isMeta;

    /** Constructs a new AlloySet object. */
    public AlloySet(String name, boolean isPrivate, boolean isMeta, AlloyType type) {
        super(name);
        this.type = type;
        this.isPrivate = isPrivate;
        this.isMeta = isMeta;
    }

    /** Returns the parent type of the AlloySet. */
    public AlloyType getType() {
        return type;
    }

    /**
     * When comparing two AlloySet objects, we first compare their names, then their
     * types. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    public int compareTo(AlloySet other) {
        if (other == null)
            return 1;
        int n = Util.slashComparator.compare(getName(), other.getName());
        return n != 0 ? n : type.compareTo(other.type);
    }

    /**
     * When comparing two AlloySet objects, we first compare their names, then their
     * types. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    public int compareTo(AlloyNodeElement other) {
        if (!(other instanceof AlloySet))
            return 1;
        AlloySet x = (AlloySet) other;
        int n = Util.slashComparator.compare(getName(), x.getName());
        return n != 0 ? n : type.compareTo(x.type);
    }

    /**
     * When comparing two AlloySet objects, we first compare their names, then their
     * types. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    @Override
    public int compareTo(AlloyElement other) {
        if (other instanceof AlloyRelation)
            return -1;
        if (!(other instanceof AlloySet))
            return 1;
        AlloySet x = (AlloySet) other;
        int n = Util.slashComparator.compare(getName(), x.getName());
        return n != 0 ? n : type.compareTo(x.type);
    }

    /**
     * This value is used to display this type in the Visualizer's customization
     * screen.
     */
    @Override
    public String toString() {
        return getName() + " :  " + getType().getName();
    }

    /**
     * Two sets are equal if they have the same name and the same type.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloySet))
            return false;
        if (other == this)
            return true;
        AlloySet otherSet = (AlloySet) other;
        return getName().equals(otherSet.getName()) && type.equals(otherSet.type);
    }

    /** Compute a hash code based on the name and the type. */
    @Override
    public int hashCode() {
        return 5 * type.hashCode() + 7 * getName().hashCode();
    }
}
