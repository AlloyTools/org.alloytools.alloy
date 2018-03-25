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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * This utility class performs projection of AlloyModel and AlloyInstance.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class StaticProjector {

    /**
     * Constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private StaticProjector() {}

    /**
     * Given an unprojected model, project it over the given collection of
     * AlloyType(s).
     *
     * @param unprojectedModel - the original unprojected model
     * @param typesToBeProjected - the collection of types to project over
     */
    public static AlloyModel project(AlloyModel unprojectedModel, Collection<AlloyType> typesToBeProjected) {
        return project(unprojectedModel, typesToBeProjected, null);
    }

    /**
     * Given an unprojected model, project it over the given collection of
     * AlloyType(s).
     *
     * @param unprojectedModel - the original unprojected model
     * @param typesToBeProjected - the collection of types to project over
     * @param data - if nonnull, this method will record into this map how the
     *            relations are changed by the projection
     *            <p>
     *            For every relation R that gets altered to become a new AlloySet or
     *            a new AlloyRelation, data.get(R) will give us a list of integers
     *            indicating the columns deleted from R due to the projection. (For
     *            example, if an original relation A->B->C->D becomes B->D, then the
     *            list of integers will be (0,2) indicating the first and third
     *            columns were removed).
     *            <p>
     *            If a relation R remains unchanged during the projection, then
     *            data.get(R) will return an empty list.
     *            <p>
     *            If a relation R is totally deleted, due to the projection, then R
     *            won't be in data.keySet().
     */
    private static AlloyModel project(AlloyModel unprojectedModel, Collection<AlloyType> typesToBeProjected, Map<AlloyRelation,List<Integer>> data) {
        Set<AlloyType> types = new LinkedHashSet<AlloyType>(unprojectedModel.getTypes());
        List<AlloySet> sets = new ArrayList<AlloySet>(unprojectedModel.getSets());
        List<AlloyRelation> relations = new ArrayList<AlloyRelation>();
        // Get rid of all projected types, as well as their subtypes.
        for (AlloyType type : typesToBeProjected) {
            types.remove(type);
            types.removeAll(unprojectedModel.getSubTypes(type));
        }
        types.add(AlloyType.UNIV); // "univ" has to be a type
        // Now go over the relations...
        for (AlloyRelation rel : unprojectedModel.getRelations()) {
            List<AlloyType> relTypes = new ArrayList<AlloyType>(rel.getTypes());
            List<Integer> indices = new ArrayList<Integer>();
            int currentIndex = 0;
            // For each type in a relation, if it is a removed type, remove it
            // and keep track of its index.
            for (Iterator<AlloyType> relTypesIter = relTypes.iterator(); relTypesIter.hasNext();) {
                if (!types.contains(relTypesIter.next())) {
                    relTypesIter.remove();
                    indices.add(currentIndex);
                }
                currentIndex++;
            }
            // If the relation still contains at least two types, it becomes a
            // new relation
            if (relTypes.size() > 1) {
                relations.add(new AlloyRelation(rel.getName(), rel.isPrivate, rel.isMeta, relTypes));
                if (data != null)
                    data.put(rel, indices);
            }
            // If it contains only one type, it becomes a new set.
            else if (relTypes.size() == 1) {
                sets.add(new AlloySet(rel.getName(), rel.isPrivate, rel.isMeta, relTypes.get(0)));
                if (data != null)
                    data.put(rel, indices);
            }
        }
        // Finally, go through the sets and remove any whose type was removed.
        for (Iterator<AlloySet> setsIter = sets.iterator(); setsIter.hasNext();) {
            AlloySet set = setsIter.next();
            if (!types.contains(set.getType()))
                setsIter.remove();
        }
        return new AlloyModel(types, sets, relations, unprojectedModel);
    }

    /**
     * Project an instance over the given list of types (and their associated chosen
     * atom).
     *
     * @param oldInstance - the original unprojected instance
     * @param projection - the list of types to be projected and their associated
     *            chosen atoms
     *            <p>
     *            For each type t in projection.getProjectedTypes:
     *            <p>
     *            (1) If t doesn't exist in the instance, then we will simply ignore
     *            t.
     *            <p>
     *            (2) Otherwise, if t has one or more atoms in the original
     *            instance, <br>
     *            then projection.getProjectedAtom(t) must be one of the atoms
     *            (indicating the chosen atom for that type) <br>
     *            else projection.getProjectedAtom(t) must be null. <br>
     *            If rule (2) is violated, then some tuples may not show up in the
     *            return value.
     */
    public static AlloyInstance project(AlloyInstance oldInstance, AlloyProjection projection) {
        Map<AlloyRelation,List<Integer>> data = new LinkedHashMap<AlloyRelation,List<Integer>>();
        Map<AlloyAtom,Set<AlloySet>> atom2sets = new LinkedHashMap<AlloyAtom,Set<AlloySet>>();
        Map<AlloyRelation,Set<AlloyTuple>> rel2tuples = new LinkedHashMap<AlloyRelation,Set<AlloyTuple>>();
        AlloyModel newModel = project(oldInstance.model, projection.getProjectedTypes(), data);
        // First put all the atoms from the old instance into the new one
        for (AlloyAtom atom : oldInstance.getAllAtoms()) {
            atom2sets.put(atom, new LinkedHashSet<AlloySet>(oldInstance.atom2sets(atom)));
        }
        // Now, decide what tuples to generate
        for (AlloyRelation r : oldInstance.model.getRelations()) {
            List<Integer> list = data.get(r);
            if (list == null)
                continue; // This means that relation was deleted entirely
            tupleLabel: for (AlloyTuple oldTuple : oldInstance.relation2tuples(r)) {
                for (Integer i : list) {
                    // If an atom in the original tuple should be projected, but
                    // it doesn't match the
                    // chosen atom for that type, then this tuple must not be
                    // included in the new instance
                    AlloyAtom a = oldTuple.getAtoms().get(i);
                    AlloyType bt = r.getTypes().get(i);
                    bt = oldInstance.model.getTopmostSuperType(bt);
                    if (!a.equals(projection.getProjectedAtom(bt)))
                        continue tupleLabel;
                }
                List<AlloyAtom> newTuple = oldTuple.project(list);
                List<AlloyType> newObj = r.project(list);
                if (newObj.size() > 1 && newTuple.size() > 1) {
                    AlloyRelation r2 = new AlloyRelation(r.getName(), r.isPrivate, r.isMeta, newObj);
                    Set<AlloyTuple> answer = rel2tuples.get(r2);
                    if (answer == null)
                        rel2tuples.put(r2, answer = new LinkedHashSet<AlloyTuple>());
                    answer.add(new AlloyTuple(newTuple));
                } else if (newObj.size() == 1 && newTuple.size() == 1) {
                    AlloyAtom a = newTuple.get(0);
                    Set<AlloySet> answer = atom2sets.get(a);
                    if (answer == null)
                        atom2sets.put(a, answer = new LinkedHashSet<AlloySet>());
                    answer.add(new AlloySet(r.getName(), r.isPrivate, r.isMeta, newObj.get(0)));
                }
            }
        }
        // Here, we don't have to explicitly filter out "illegal"
        // atoms/tuples/...
        // (that is, atoms that belong to types that no longer exist, etc).
        // That's because AlloyInstance's constructor must do the check too, so
        // there's no point in doing that twice.
        return new AlloyInstance(oldInstance.originalA4, oldInstance.filename, oldInstance.commandname, newModel, atom2sets, rel2tuples, oldInstance.isMetamodel);
    }
}
