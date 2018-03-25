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
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;

/**
 * Immutable; represents an Alloy model.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class AlloyModel {

    /**
     * An unmodifiable sorted set of all types in this model.
     */
    private final Set<AlloyType>           types;

    /**
     * An unmodifiable sorted set of all sets in this model. <br>
     * AlloyModel's constructor guarantees that, for each set here, set.getType() is
     * in this.types
     */
    private final Set<AlloySet>            sets;

    /**
     * An unmodifiable sorted set of all relations in this model. <br>
     * AlloyModel's constructor guarantees that, for each relation here,
     * relation.getTypes() are in this.types
     */
    private final Set<AlloyRelation>       relations;

    /**
     * If A extends B, then "(A,B)" will be in this map.
     * <p>
     * AlloyModel's constructor ensures the following: <br>
     * (1) hierachy.keySet() is always a subset of this.types <br>
     * (2) hierachy.valueSet() is always a subset of this.types <br>
     * (3) "univ" is never in the keySet <br>
     * (4) null is never in the keySet nor valueSet <br>
     * (5) there is no cycle in this relation
     */
    private final Map<AlloyType,AlloyType> hierarchy;

    /**
     * The map from name to AlloyType. <br>
     * AlloyModel's constructor guarantees that this.name2types.values() has the
     * same entries as this.types
     */
    private final Map<String,AlloyType>    name2types = new HashMap<String,AlloyType>();

    /**
     * Returns true iff the nodes x, map.get(x), map.get(map.get(x))... form an
     * infinite chain of nonnull objects.
     *
     * @param map - a map from AlloyType to AlloyType
     * @param x - the AlloyType object we want to check
     */
    public static boolean isCycle(Map<AlloyType,AlloyType> map, AlloyType x) {
        int i = (-5), n = map.size();
        while (x != null) {
            x = map.get(x);
            i++;
            if (i >= n)
                return true;
        }
        return false;
    }

    /**
     * Construct a new AlloyModel object.
     *
     * @param types - the types; we will always add "univ" to it if it's not there
     *            already
     * @param sets - the sets
     * @param rels - the relations
     * @param map - we consult this "sig to parent sig" map and extract the mappings
     *            relevant to this model. (If we detect a cycle, we will arbitrarily
     *            break the cycle)
     */
    public AlloyModel(Collection<AlloyType> types, Collection<AlloySet> sets, Collection<AlloyRelation> rels, Map<AlloyType,AlloyType> map) {
        // The following 3 have to be tree sets, since we want to keep them
        // sorted
        Set<AlloyType> allTypes = new TreeSet<AlloyType>();
        Set<AlloySet> allSets = new TreeSet<AlloySet>();
        Set<AlloyRelation> allRelations = new TreeSet<AlloyRelation>();
        allTypes.addAll(types);
        allTypes.add(AlloyType.UNIV);
        for (AlloySet s : sets)
            if (allTypes.contains(s.getType()))
                allSets.add(s);
        for (AlloyRelation r : rels)
            if (allTypes.containsAll(r.getTypes()))
                allRelations.add(r);
        this.types = Collections.unmodifiableSet(allTypes);
        this.sets = Collections.unmodifiableSet(allSets);
        this.relations = Collections.unmodifiableSet(allRelations);
        Map<AlloyType,AlloyType> newmap = new LinkedHashMap<AlloyType,AlloyType>();
        for (AlloyType type : allTypes) {
            AlloyType sup = isCycle(map, type) ? null : map.get(type);
            if (sup == null || !allTypes.contains(sup))
                sup = AlloyType.UNIV;
            newmap.put(type, sup);
        }
        newmap.remove(AlloyType.UNIV); // This ensures univ is not in
                                      // hierarchy's keySet
        this.hierarchy = Collections.unmodifiableMap(newmap);
        for (AlloyType t : this.types)
            this.name2types.put(t.getName(), t);
    }

    /**
     * Construct a new AlloyModel object.
     *
     * @param types - the types ; we will always add "univ" to it if it's not there
     *            already
     * @param sets - the sets
     * @param rels - the relations
     * @param old - we consult this model's "sig to parent sig" map, and extract the
     *            mappings relevant to this model.
     */
    public AlloyModel(Collection<AlloyType> types, Collection<AlloySet> sets, Collection<AlloyRelation> rels, AlloyModel old) {
        this(types, sets, rels, old.hierarchy);
    }

    /**
     * If type==univ, return null; otherwise, return a nonnull AlloyType object
     * representing its super type. <br>
     * (In particular, if "type" does not exist in this model, we'll return "univ"
     * as the answer).
     */
    public AlloyType getSuperType(AlloyType type) {
        if (type.getName().equals("univ"))
            return null;
        AlloyType answer = hierarchy.get(type);
        return answer == null ? AlloyType.UNIV : answer;
    }

    /**
     * If type==univ, return null; otherwise, return a nonnull AlloyType object
     * representing its topmost non-univ super type.
     * <p>
     * Thus, if "type" is in this model, but its supertype is univ, then we'll
     * return type as-is.
     * <p>
     * Note: if "type" does not exist in this model, we'll return it as-is.
     */
    public AlloyType getTopmostSuperType(AlloyType type) {
        if (type == null || type.equals(AlloyType.UNIV))
            return null;
        while (true) {
            AlloyType top = getSuperType(type);
            if (top == null || top.equals(AlloyType.UNIV))
                break;
            type = top;
        }
        return type;
    }

    /**
     * Returns a sorted, unmodifiable list of types that are direct or indirect
     * subtypes of the given type. <br>
     * This method will search recursively, so if the subtypes themselves have
     * subtypes, they too are included. <br>
     * If type==null, or it does not exist in this model, or it has no subsigs, then
     * we return an empty set.
     */
    public ConstList<AlloyType> getSubTypes(AlloyType type) {
        TempList<AlloyType> subtypes = new TempList<AlloyType>();
        for (AlloyType subType : types)
            if (isSubtype(subType, type))
                subtypes.add(subType);
        return subtypes.makeConst(); // Since this.types is sorted, the result
                                    // is already sorted.
    }

    /**
     * Returns a sorted, unmodifiable list of types that are direct subtypes of the
     * given type. <br>
     * This method will only return types that are direct subtypes of the given
     * argument. <br>
     * If type==null, or it does not exist in this model, or it has no subsigs, then
     * we return an empty set.
     */
    public ConstList<AlloyType> getDirectSubTypes(AlloyType type) {
        TempList<AlloyType> subtypes = new TempList<AlloyType>();
        for (AlloyType subType : types)
            if (isDirectSubtype(subType, type))
                subtypes.add(subType);
        return subtypes.makeConst(); // Since this.types is sorted, the result
                                    // is already sorted.
    }

    /**
     * Returns true iff "subType" is a direct or indirect subsig of "superType".
     * <br>
     * If subType==null or superType==null, it always returns false.
     */
    public boolean isSubtype(AlloyType subType, AlloyType superType) {
        if (subType == null || superType == null || !types.contains(subType) || subType.equals(AlloyType.UNIV))
            return false;
        while (subType != null) {
            subType = getSuperType(subType); // Do this before calling equals(),
                                            // since we want
                                            // isSubtype(X,X)==false
            if (superType.equals(subType))
                return true;
        }
        return false;
    }

    /**
     * Returns true iff "subType" is a direct subsig of "superType". <br>
     * If subType==null or superType==null, it always returns false.
     */
    public boolean isDirectSubtype(AlloyType subType, AlloyType superType) {
        if (subType == null || superType == null || !types.contains(subType) || subType.equals(AlloyType.UNIV))
            return false;
        if (superType.equals(AlloyType.UNIV) && hierarchy.get(subType) == null)
            return true;
        return superType.equals(hierarchy.get(subType));
    }

    /**
     * Returns true iff "subType" is equal to, or is a direct or indirect subsig of
     * "superType". <br>
     * If subType==null or superType==null, it always returns false.
     */
    public boolean isEqualOrSubtype(AlloyType subType, AlloyType superType) {
        if (superType == null)
            return false;
        while (subType != null) {
            if (superType.equals(subType))
                return true;
            subType = getSuperType(subType);
        }
        return false;
    }

    /**
     * Two AlloyModel objects are equal if they have the same types, sets,
     * relations, and extension relationship.
     */
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof AlloyModel))
            return false;
        if (other == this)
            return true;
        AlloyModel x = (AlloyModel) other;
        return types.equals(x.types) && sets.equals(x.sets) && relations.equals(x.relations) && hierarchy.equals(x.hierarchy);
    }

    /**
     * Compute a hashcode based on the types, sets, relations, and the extension
     * relationship.
     */
    @Override
    public int hashCode() {
        return types.hashCode() + 3 * sets.hashCode() + 5 * relations.hashCode() + 7 * hierarchy.hashCode();
    }

    /** Returns true if this model contains the given type. */
    public boolean hasType(AlloyType type) {
        return types.contains(type);
    }

    /**
     * Returns the AlloyType object if this model contains the given type; or return
     * null otherwise.
     */
    public AlloyType hasType(String name) {
        return name2types.get(name);
    }

    /**
     * Returns the AlloyRelation object if this model contains the given relation;
     * or return null otherwise.
     */
    public AlloySet hasSet(String name, AlloyType type) {
        for (AlloySet s : sets)
            if (s.getName().equals(name) && s.getType().equals(type))
                return s;
        return null;
    }

    /**
     * Returns the AlloyRelation object if this model contains the given relation;
     * or return null otherwise.
     */
    public AlloyRelation hasRelation(String name, List<AlloyType> types) {
        for (AlloyRelation r : relations)
            if (r.getName().equals(name) && r.getTypes().equals(types))
                return r;
        return null;
    }

    /**
     * Returns an unmodifiable sorted set of all AlloyType(s) in this model.
     */
    public Set<AlloyType> getTypes() {
        return types;
    }

    /**
     * Returns an unmodifiable sorted set of all AlloySet(s) in this model.
     */
    public Set<AlloySet> getSets() {
        return sets;
    }

    /**
     * Returns an unmodifiable sorted set of all AlloyRelation(s) in this model.
     */
    public Set<AlloyRelation> getRelations() {
        return relations;
    }
}
