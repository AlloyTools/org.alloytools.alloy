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
 * Immutable; represents an Alloy toplevel signature or an Alloy subsignature.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyType extends AlloyNodeElement {

    /**
     * This caches an instance of the "univ" AlloyType, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyType UNIV   = new AlloyType("univ", false, false, true, false, false, false);

    /**
     * This caches an instance of the "Int" AlloyType, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyType INT    = new AlloyType("Int", false, false, true, false, false, false);

    /**
     * This caches an instance of the "seq/Int" AlloyType, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyType SEQINT = new AlloyType("seq/Int", false, false, true, false, false, false);

    /**
     * This caches an instance of the "String" AlloyType, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyType STRING = new AlloyType("String", false, false, true, false, false, false);

    /**
     * This caches an instance of the "set" AlloyType, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyType SET    = new AlloyType("set", false, false, false, false, false, false);

    /** Constructs an AlloyType object with that name. */
    public AlloyType(String name, boolean isOne, boolean isAbstract, boolean isBuiltin, boolean isPrivate, boolean isMeta, boolean isEnum) {
        super(name);
        this.isOne = isOne;
        this.isAbstract = isAbstract;
        this.isBuiltin = isBuiltin;
        this.isPrivate = isPrivate;
        this.isMeta = isMeta;
        this.isEnum = isEnum;
    }

    /**
     * Records whether this sig is known to be "one"; NOTE: this value is NOT USED
     * during equals() comparison.
     */
    public final boolean isOne;

    /**
     * Records whether this sig is known to be "abstract"; NOTE: this value is NOT
     * USED during equals() comparison.
     */
    public final boolean isAbstract;

    /**
     * Records whether this sig is known to be "builtin"; NOTE: this value is NOT
     * USED during equals() comparison.
     */
    public final boolean isBuiltin;

    /**
     * Records whether this sig is known to be "private"; NOTE: this value is NOT
     * USED during equals() comparison.
     */
    public final boolean isPrivate;

    /**
     * Records whether this sig is known to be "meta"; NOTE: this value is NOT USED
     * during equals() comparison.
     */
    public final boolean isMeta;

    /**
     * Records whether this sig is known to be "enum"; NOTE: this value is NOT USED
     * during equals() comparison.
     */
    public final boolean isEnum;

    /**
     * When comparing two AlloyType objects, we compare their names. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    public int compareTo(AlloyType other) {
        if (other == null)
            return 1;
        return Util.slashComparator.compare(getName(), other.getName());
    }

    /**
     * When comparing two AlloyType objects, we compare their names. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    public int compareTo(AlloyNodeElement other) {
        if (other == null)
            return 1;
        if (!(other instanceof AlloyType))
            return -1;
        return Util.slashComparator.compare(getName(), ((AlloyType) other).getName());
    }

    /**
     * When comparing two AlloyType objects, we compare their names. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    @Override
    public int compareTo(AlloyElement other) {
        if (other == null)
            return 1;
        if (!(other instanceof AlloyType))
            return -1;
        return Util.slashComparator.compare(getName(), ((AlloyType) other).getName());
    }

    /**
     * This value is used to display this type in the Visualizer's customization
     * screen.
     */
    @Override
    public String toString() {
        return getName();
    }

    /** Two types are equal if they have the same name. */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyType))
            return false;
        if (other == this)
            return true;
        return getName().equals(((AlloyType) other).getName());
    }

    /** Compute a hash code based on the name. */
    @Override
    public int hashCode() {
        return getName().hashCode();
    }
}
