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
import java.util.Collections;
import java.util.Map;
import java.util.TreeMap;

/**
 * Immutable; represents a set of types to be projected, plus the exact atom
 * chosen for each type to be projected.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyProjection {

    /**
     * Its keySet is the set of types to be projected; each type is associated with
     * the atom chosen to be projected.
     * <p>
     * Its keySet is guaranteed to be sorted.
     * <p>
     * For each type t in the keyset, map.get(t) is an AlloyAtom (indicating the
     * atom in t that we chose to project over).
     * <p>
     * Note: there's no way for this class to confirm that a chosen atom is really
     * in that type (since the atom may be in a subtype, and thus the atom.type()
     * won't be exactly the same as t). Thus, classes that use AlloyProjection
     * objects need to do their own sanity check.
     */
    private final Map<AlloyType,AlloyAtom> map;

    /**
     * Constructs a new AlloyProjection object based on the set of types to be
     * projected and the exact atoms chosen.
     *
     * @param map - this map describes the set of types to be projected and the
     *            exact atoms chosen to be projected
     *            <p>
     *            For each type t in map.keySet(), <br>
     *            map.get(t) is an AlloyAtom (indicating the atom in t that we chose
     *            to project over).
     *            <p>
     *            Note: there's no way for this class to confirm that a chosen atom
     *            is really in that type (since the atom may be in a subtype, and
     *            thus the atom.type() won't be exactly the same). Thus, classes
     *            that use AlloyProjection objects need to do their own sanity
     *            check.
     */
    public AlloyProjection(Map<AlloyType,AlloyAtom> map) {
        Map<AlloyType,AlloyAtom> mymap = new TreeMap<AlloyType,AlloyAtom>();
        for (Map.Entry<AlloyType,AlloyAtom> e : map.entrySet()) {
            if (e.getKey() != null && e.getValue() != null)
                mymap.put(e.getKey(), e.getValue());
        }
        this.map = Collections.unmodifiableMap(mymap);
    }

    /**
     * Constructs an empty AlloyProjection object, with an empty projection list.
     */
    public AlloyProjection() {
        this.map = Collections.unmodifiableMap(new TreeMap<AlloyType,AlloyAtom>());
    }

    /**
     * Return the sorted unmodifiable collection of types we are projecting.
     */
    public Collection<AlloyType> getProjectedTypes() {
        return map.keySet();
    }

    /**
     * Return the atom chosen for that type; returns null if that type is not
     * projected.
     */
    public AlloyAtom getProjectedAtom(AlloyType type) {
        return map.get(type);
    }

    /** Returns a human readable dump of this object. */
    @Override
    public String toString() {
        boolean first = true;
        String ans = "Projection[";
        for (Map.Entry<AlloyType,AlloyAtom> e : map.entrySet()) {
            if (first)
                first = false;
            else
                ans = ans + ", ";
            ans = ans + e.getKey().getName() + ":" + e.getValue().getVizName(null, true);
        }
        return ans + "]";
    }

    /**
     * AlloyProjections are equal if they are projecting over the same types, each
     * type with the same chosen value.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyProjection))
            return false;
        if (other == this)
            return true;
        return map.equals(((AlloyProjection) other).map);
    }

    /**
     * Computes a hashcode based on the types and the atoms chosen for each type.
     */
    @Override
    public int hashCode() {
        return map.hashCode();
    }
}
