/* Alloy Analyzer 4 -- Copyright (c) 2007-2008, Derek Rayside
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

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4graph.DotColor;

/**
 * This class implements the automatic visualization inference.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

final class MagicLayout {

    /** The VizState object that we're going to configure. */
    private final VizState     vizState;

    private Set<AlloyType>     enumerationTypes = new LinkedHashSet<AlloyType>();
    private Set<AlloyType>     singletonTypes   = new LinkedHashSet<AlloyType>();
    private AlloyType          projectionType   = null;
    private Set<AlloyRelation> spineRelations   = Collections.emptySet();

    /** Constructor. */
    private MagicLayout(final VizState vizState) {
        this.vizState = vizState;
    }

    /** Main method to infer settings. */
    public static void magic(final VizState vizState) {
        vizState.resetTheme();
        final MagicLayout st = new MagicLayout(vizState);
        st.identifyEnumerationTypes();
        st.projection();
        st.nodeVisibility();
        st.spine();
        st.attributes();
        st.edgeLabels();
    }

    /**
     * SYNTACTIC: An enumeration follows the pattern "abstract sig Colour; one sig
     * Red; one sig Blue".
     */
    private void identifyEnumerationTypes() {
        final AlloyModel model = vizState.getCurrentModel();
        final Set<AlloyType> types = model.getTypes();
        for (final AlloyType t : types) {
            if (enumerationTypes.contains(t))
                continue; // we've already checked this one, don't muck with it
                         // now
            if (t.isOne)
                singletonTypes.add(t);
            if (!t.isBuiltin && t.isAbstract) {
                List<AlloyType> subTypes = model.getSubTypes(t);
                int numberOfSingletonSubtypes = 0;
                for (AlloyType st : subTypes) {
                    if (st.isOne) {
                        numberOfSingletonSubtypes++;
                        singletonTypes.add(st);
                    }
                }
                if (subTypes.size() == numberOfSingletonSubtypes) { // we have a
                                                                   // winner!
                    enumerationTypes.add(t);
                    enumerationTypes.addAll(subTypes);
                    for (final AlloyType st : subTypes) {
                        // all of the subtypes in the enumeration should have
                        // visibility inherited
                        // so that the user only needs to make the abstract
                        // supertype visible if we made a mistake hiding these
                        // things
                        vizState.nodeVisible.put(st, null);
                    }
                    // hide unless these are the source of some relation
                    boolean visible = false;
                    for (AlloyRelation r : model.getRelations()) {
                        AlloyType sourceType = r.getTypes().get(0);
                        if (t.equals(sourceType) || subTypes.contains(sourceType)) {
                            visible = true;
                            break;
                        }
                    }
                    vizState.nodeVisible.put(t, visible); // log("VizInference:
                                                         // visible status of
                                                         // enumeration type
                                                         // " + t + " " +
                                                         // visible);
                }
            }
        }

    }

    /**
     * SEMANTIC/LAYOUT: Determine at most one relation to project over. When do we
     * project over a sig? Do we ever project over more than one?
     * <ul>
     * <li>pick 0 or 1 things to project over
     * <li>match names: Time, State, Tick, TimeStep
     * <li>if ord is opened over the sig
     * <li>if present in several ternary relations (i.e. if it will help viz high
     * arity relations)
     * <li>position in relation (always end or always beginning)
     * <li>should we try to catch projections such as the one over birthday books?
     * <li>pattern match (b,b') to catch transition relations
     * <li>add combo box in GUI (?)
     * </ul>
     */
    private void projection() {
        // only fiddle with this if it hasn't already been set somewhere else
        if (projectionType == null && vizState.getProjectedTypes().isEmpty()) {
            AlloyModel model = vizState.getCurrentModel();
            // final Set<AlloyType> candidateTypes = new HashSet<AlloyType>();
            Map<AlloyType,Integer> scores = new LinkedHashMap<AlloyType,Integer>();
            for (AlloyType t : model.getTypes()) {
                scores.put(t, 0);
                // does it have a name like State, Time, etc
                if (hasLikelyProjectionTypeName(t.getName())) {
                    scores.put(t, scores.get(t) + 1);
                }
                // is it in some ternary relation?
                for (AlloyRelation r : model.getRelations()) {
                    if (r.getArity() > 2 && r.getTypes().contains(t))
                        scores.put(t, scores.get(t) + 1);
                }
            }
            // now we have the scores, see who the winners are:
            int max = 0;
            final Set<AlloyType> winners = new LinkedHashSet<AlloyType>();
            for (final Map.Entry<AlloyType,Integer> e : scores.entrySet()) {
                if (e.getValue() == max)
                    winners.add(e.getKey());
                if (e.getValue() > max) {
                    max = e.getValue();
                    winners.clear();
                    winners.add(e.getKey());
                }
            }
            if (max < 2) {
                // no winner, don't project
                // log("VizInference: no candidate type to project on.");
            } else {
                if (winners.size() > 1) {
                    // we have a tie ... what to do?
                    // log("VizInference: projection tie. " + winners);
                }
                final AlloyType winner = winners.iterator().next();
                // pick one arbitrarily for now ...
                // log("VizInference: projecting on " + max + " " + winner);
                projectionType = winner;
                vizState.project(projectionType);
            }

        }
    }

    private final static ConstList<String> LIKELY_PROJECTION_TYPE_NAMES = Util.asList("State", "TrainState", "Time", "Tick", "TimeStep");

    private final boolean hasLikelyProjectionTypeName(final String n) {
        for (String s : LIKELY_PROJECTION_TYPE_NAMES)
            if (n.startsWith(s) || n.endsWith(s))
                return true;
        return false;
    }

    /**
     * SEMANTIC/LAYOUT: Determine some relations to be the spine (ie, influence the
     * layout). Which relations should be used to layout? all? none? clever?
     * <ul>
     * <li>interesting example: 2d game grid
     * <li>ex: toplogical sort -- layout tree and list, not cnxn between them
     * <li>look for homogenius binary relation (a -&gt; a)
     * <li>may be several relations defining the spine
     * </ul>
     */
    private void spine() {
        AlloyModel model = vizState.getCurrentModel();
        Set<AlloyRelation> relations = model.getRelations();
        if (!relations.isEmpty()) {
            // only mess with the relations if there are some
            // only binary relations are candidates
            Set<AlloyRelation> spines = new LinkedHashSet<AlloyRelation>();
            for (AlloyRelation r : relations) {
                if (r.getArity() == 2) {
                    List<AlloyType> rtypes = r.getTypes();
                    AlloyType targetType = rtypes.get(1);
                    // only a spine if the target is not an enumeration type
                    if (!enumerationTypes.contains(targetType)) {
                        spines.add(r);
                    }
                    // however, binary relations named parent should be layed
                    // out backwards
                    if (r.getName().equals("parent")) {
                        vizState.layoutBack.put(r, true);
                    }
                }
            }
            // do we have any spines? if so, use them, if not use all relations
            spineRelations = spines.isEmpty() ? relations : spines;
        }
        // set everything to not influence layout
        for (AlloyRelation r : relations) {
            vizState.constraint.put(r, false);
            vizState.edgeColor.put(r, DotColor.GRAY);
        }
        // set spines to influence layout
        for (AlloyRelation s : spineRelations) {
            vizState.constraint.put(s, null);
            // inherit the default color, which should be black
            vizState.edgeColor.put(s, null);
        }

    }

    /**
     * SEMANTIC/LAYOUT: Determine whether non-projection, non-spine relations should
     * be shown as attributes or edges.
     * <ul>
     * <li>binary vs. higher arity -- only make binary attributes
     * <li>use attributes on-demand to reduce clutter, not blindly
     * <li>functional relations should be attributes (what about a tree?)
     * <li>never make something an edge and an attribute
     * </ul>
     */
    private void attributes() {
        AlloyModel model = vizState.getCurrentModel();
        for (AlloyRelation r : model.getRelations()) {
            List<AlloyType> rTypes = r.getTypes();
            if (r.getArity() == 2 && !rTypes.contains(projectionType) && !spineRelations.contains(r)) {
                // it's binary, non-projection and non-spine
                AlloyType targetType = rTypes.get(1);
                if (enumerationTypes.contains(targetType)) {
                    // target is an enumeration: we have an attribute
                    vizState.attribute.put(r, true);
                    vizState.edgeVisible.put(r, false);
                }
            }
        }
    }

    /** PRESENTATIONAL: Labels for edges. */
    private void edgeLabels() {
        AlloyModel model = vizState.getCurrentModel();
        int relationsAsEdges = 0;
        AlloyRelation visibleRelation = null;
        for (AlloyRelation r : model.getRelations()) {
            Boolean v = vizState.edgeVisible.get(r);
            if (v == null || v.booleanValue()) {
                // it's visible
                relationsAsEdges++;
                visibleRelation = r;
                // remove text before last slash
                MagicUtil.trimLabelBeforeLastSlash(vizState, r);
            }
        }
        // If there's only one relation visible as an edge, and it's binary,
        // then no need to label it.
        if (1 == relationsAsEdges && visibleRelation.getArity() == 2) {
            vizState.label.put(visibleRelation, "");
        }
    }

    /** SYNTACTIC/VISUAL: Hide some things. */
    private void nodeVisibility() {
        AlloyModel model = vizState.getCurrentModel();
        Set<AlloyType> types = model.getTypes();
        for (AlloyType t : types)
            if (!t.isBuiltin && MagicUtil.isActuallyVisible(vizState, t) && t.getName().endsWith("/Ord")) {
                vizState.nodeVisible.put(t, false);
            }
        for (AlloySet s : model.getSets())
            if (MagicUtil.isActuallyVisible(vizState, s) && s.getName().endsWith("/Ord")) {
                vizState.nodeVisible.put(s, false);
            }

    }
}
