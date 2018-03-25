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

import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Util;

/**
 * Immutable; represents an Alloy relation of 2 or higher arity.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyRelation extends AlloyElement {

    /**
     * This caches an instance of the "extends" AlloyRelation, so we don't have to
     * keep re-constructing it.
     */
    public static final AlloyRelation  EXTENDS = new AlloyRelation("extends", false, false, Util.asList(AlloyType.UNIV, AlloyType.UNIV));

    /**
     * This caches an instance of the "in" AlloyRelation, so we don't have to keep
     * re-constructing it.
     */
    public static final AlloyRelation  IN      = new AlloyRelation("in", false, false, Util.asList(AlloyType.SET, AlloyType.UNIV));

    /** The unmodifiable list of types. */
    private final ConstList<AlloyType> types;

    /**
     * Records whether this relation is known to be "private"; NOTE: this value is
     * NOT USED during equals() comparison.
     */
    public final boolean               isPrivate;

    /**
     * Records whether this relation is known to be "meta"; NOTE: this value is NOT
     * USED during equals() comparison.
     */
    public final boolean               isMeta;

    /**
     * Constructs a new AlloyRelation with that name and that list of types;
     * types.size() must be 2 or above.
     */
    public AlloyRelation(String name, boolean isPrivate, boolean isMeta, List<AlloyType> types) {
        super(name);
        if (types == null || types.size() < 2)
            throw new RuntimeException("An AlloyRelation object must have 2 or more types.");
        this.types = ConstList.make(types);
        this.isPrivate = isPrivate;
        this.isMeta = isMeta;
    }

    /**
     * Project this relation and return an unmodifiable list of remaining types
     * (after removing zero or more columns)
     *
     * @param columns - the collection of columns to remove (0 is the first column,
     *            1 is the second column...)
     */
    public List<AlloyType> project(Collection<Integer> columns) {
        TempList<AlloyType> list = new TempList<AlloyType>(types.size());
        for (int i = 0; i < types.size(); i++)
            if (!columns.contains(i))
                list.add(types.get(i));
        if (list.size() == types.size())
            return types;
        else
            return list.makeConst();
    }

    /**
     * Returns an unmodifiable list of AlloyTypes representing the relation's type.
     */
    public List<AlloyType> getTypes() {
        return types;
    }

    /** Returns the arity of the relation. */
    public int getArity() {
        return types.size();
    }

    /**
     * When comparing two AlloyRelation objects, we first compare the name, then the
     * arity, then the types. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    public int compareTo(AlloyRelation other) {
        if (other == null)
            return 1;
        // First compare the names.
        int n = Util.slashComparator.compare(getName(), other.getName());
        if (n != 0)
            return n;
        // Now compare the arity of the two relations
        int arity = types.size();
        if (arity != other.types.size())
            return (arity < other.types.size()) ? -1 : 1;
        // Finally, compare each AlloyType
        for (int i = 0; i < arity; i++) {
            n = types.get(i).compareTo(other.types.get(i));
            if (n != 0)
                return n;
        }
        return 0;
    }

    /**
     * When comparing two AlloyRelation objects, we first compare the name, then the
     * arity, then the types. <br>
     * We guarantee x.equals(y) iff x.compareTo(y)==0
     */
    @Override
    public int compareTo(AlloyElement other) {
        if (!(other instanceof AlloyRelation))
            return 1;
        return compareTo((AlloyRelation) other);
    }

    /**
     * This value is used to display this type in the Visualizer's customization
     * screen.
     */
    @Override
    public String toString() {
        String answer = "";
        boolean first = true;
        for (AlloyType type : getTypes()) {
            if (first) {
                first = false;
                answer = answer + getName() + " :  ";
            } else
                answer = answer + " -> ";
            answer = answer + type.getName();
        }
        return answer;
    }

    /**
     * Two relations are equal if they have the same name, and the same list of
     * types.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyRelation))
            return false;
        if (other == this)
            return true;
        AlloyRelation otherRelation = (AlloyRelation) other;
        return getName().equals(otherRelation.getName()) && types.equals(otherRelation.types);
    }

    /**
     * Computes a hash code based on the name and the list of types.
     */
    @Override
    public int hashCode() {
        return 5 * getName().hashCode() + 7 * types.hashCode();
    }
}
