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

import static edu.mit.csail.sdg.alloy4graph.DotShape.BOX;
import static edu.mit.csail.sdg.alloy4graph.DotShape.DIAMOND;
import static edu.mit.csail.sdg.alloy4graph.DotShape.DOUBLE_OCTAGON;
import static edu.mit.csail.sdg.alloy4graph.DotShape.EGG;
import static edu.mit.csail.sdg.alloy4graph.DotShape.ELLIPSE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.HEXAGON;
import static edu.mit.csail.sdg.alloy4graph.DotShape.HOUSE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.INV_HOUSE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.INV_TRAPEZOID;
import static edu.mit.csail.sdg.alloy4graph.DotShape.INV_TRIANGLE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.M_CIRCLE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.M_DIAMOND;
import static edu.mit.csail.sdg.alloy4graph.DotShape.M_SQUARE;
import static edu.mit.csail.sdg.alloy4graph.DotShape.OCTAGON;
import static edu.mit.csail.sdg.alloy4graph.DotShape.PARALLELOGRAM;
import static edu.mit.csail.sdg.alloy4graph.DotShape.TRAPEZOID;
import static edu.mit.csail.sdg.alloy4graph.DotShape.TRIPLE_OCTAGON;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4graph.DotColor;
import edu.mit.csail.sdg.alloy4graph.DotPalette;
import edu.mit.csail.sdg.alloy4graph.DotShape;
import edu.mit.csail.sdg.alloy4graph.DotStyle;

/**
 * This class implements the automatic visualization inference.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

final class MagicColor {

    /** The VizState object that we're going to configure. */
    private final VizState vizState;

    /** Constructor. */
    private MagicColor(final VizState vizState) {
        this.vizState = vizState;
    }

    /** Main method to infer settings. */
    public static void magic(final VizState vizState) {
        vizState.setNodePalette(DotPalette.MARTHA);
        final MagicColor st = new MagicColor(vizState);
        st.nodeNames();
        st.nodeShape();
        st.nodeColour();
        st.skolemColour();
    }

    /**
     * SYNTACTIC/VISUAL: Determine colours for nodes. when do we color things and
     * what is the meaning of color
     * <ul>
     * <li>symmetry breaking: colors only matter up to recoloring (diff from shape!)
     * <li>color substitutes for name/label
     * </ul>
     */
    private void nodeColour() {
        final Set<AlloyType> visibleUserTypes = MagicUtil.visibleUserTypes(vizState);
        final Set<AlloyType> uniqueColourTypes;
        if (visibleUserTypes.size() <= 5) {
            // can give every visible user type its own shape
            uniqueColourTypes = visibleUserTypes;
        } else {
            // give every top-level visible user type its own shape
            uniqueColourTypes = MagicUtil.partiallyVisibleUserTopLevelTypes(vizState);
        }
        int index = 0;
        for (final AlloyType t : uniqueColourTypes) {
            vizState.nodeColor.put(t, (DotColor) DotColor.valuesWithout(DotColor.MAGIC)[index]);
            index = (index + 1) % DotColor.valuesWithout(DotColor.MAGIC).length;
        }
    }

    /**
     * SYNTACTIC/VISUAL: Determine colour highlighting for skolem constants.
     */
    private void skolemColour() {
        final Set<AlloySet> sets = vizState.getCurrentModel().getSets();
        for (final AlloySet s : sets) {
            // change the style
            vizState.nodeStyle.put(s, DotStyle.BOLD);
            // change the label
            String label = vizState.label.get(s);
            final int lastUnderscore = label.lastIndexOf('_');
            if (lastUnderscore >= 0) {
                label = label.substring(lastUnderscore + 1);
            }
            vizState.label.put(s, label);
        }
    }

    /** The list of shape families. */
    private static final List<ConstList<DotShape>> families;
    static {
        TempList<ConstList<DotShape>> list = new TempList<ConstList<DotShape>>();
        list.add(Util.asList(BOX, TRAPEZOID, HOUSE));
        list.add(Util.asList(ELLIPSE, EGG));
        list.add(Util.asList(HEXAGON, OCTAGON, DOUBLE_OCTAGON, TRIPLE_OCTAGON));
        list.add(Util.asList(INV_TRIANGLE, INV_HOUSE, INV_TRAPEZOID));
        list.add(Util.asList(M_DIAMOND, M_SQUARE, M_CIRCLE));
        list.add(Util.asList(PARALLELOGRAM, DIAMOND));
        families = list.makeConst();
    }

    /**
     * SYNTACTIC/VISUAL: Determine shapes for nodes.
     * <ul>
     * <li>trapezoid, hexagon, rectangle, ellipse, circle, square -- no others
     * <li>actual shape matters -- do not break symmetry as with color
     * <li>ellipse by default
     * <li>circle if special extension of ellipse
     * <li>rectangle if lots of attributes
     * <li>square if special extension of rectangle
     * <li>when to use other shapes?
     * </ul>
     */
    private void nodeShape() {
        final Set<List<DotShape>> usedShapeFamilies = new LinkedHashSet<List<DotShape>>();
        final Set<AlloyType> topLevelTypes = MagicUtil.partiallyVisibleUserTopLevelTypes(vizState);

        for (final AlloyType t : topLevelTypes) {

            // get the type family
            final Set<AlloyType> subTypes = MagicUtil.visibleSubTypes(vizState, t);
            final boolean isTvisible = MagicUtil.isActuallyVisible(vizState, t);
            final int size = subTypes.size() + (isTvisible ? 1 : 0);
            // log("TopLevelType: " + t + " -- " + subTypes + " " + size);

            // match it to a shape family
            // 1. look for exact match
            boolean foundExactMatch = false;
            for (final List<DotShape> shapeFamily : families) {
                if (size == shapeFamily.size() && !usedShapeFamilies.contains(shapeFamily)) {
                    // found a match!
                    usedShapeFamilies.add(shapeFamily);
                    assignNodeShape(t, subTypes, isTvisible, shapeFamily);
                    foundExactMatch = true;
                    break;
                }
            }
            if (foundExactMatch)
                continue;
            // 2. look for approximate match
            List<DotShape> approxShapeFamily = null;
            int approxShapeFamilyDistance = Integer.MAX_VALUE;
            for (final List<DotShape> shapeFamily : families) {
                if (size <= shapeFamily.size() && !usedShapeFamilies.contains(shapeFamily)) {
                    // found a potential match
                    final int distance = shapeFamily.size() - size;
                    if (distance < approxShapeFamilyDistance) {
                        // it's a closer fit than the last match, keep it for
                        // now
                        approxShapeFamily = shapeFamily;
                        approxShapeFamilyDistance = distance;
                    }
                }
            }
            if (approxShapeFamily != null) {
                // use the best approximate match that we just found
                usedShapeFamilies.add(approxShapeFamily);
                assignNodeShape(t, subTypes, isTvisible, approxShapeFamily);
            }
            // 3. re-use a shape family matched to something else -- just give
            // up for now
        }
    }

    /** Helper for nodeShape(). */
    private void assignNodeShape(final AlloyType t, final Set<AlloyType> subTypes, final boolean isTvisible, final List<DotShape> shapeFamily) {
        int index = 0;
        // shape for t, if visible
        if (isTvisible) {
            final DotShape shape = shapeFamily.get(index++);
            // log("AssignNodeShape " + t + " " + shape);
            vizState.shape.put(t, shape);
        }
        // shapes for visible subtypes
        for (final AlloyType subt : subTypes) {
            final DotShape shape = shapeFamily.get(index++);
            // log("AssignNodeShape " + subt + " " + shape);
            vizState.shape.put(subt, shape);
        }
    }

    /**
     * SYNTACTIC/VISUAL: Should the names of nodes be displayed on them? when should
     * names be used?
     * <ul>
     * <li>not when only a single sig (e.g. state machine with only one 'node' sig)
     * <li>not when only a single relation
     * <li>check for single things _after_ hiding things by default
     * </ul>
     */
    private void nodeNames() {
        final Set<AlloyType> visibleUserTypes = MagicUtil.visibleUserTypes(vizState);
        // trim names
        for (final AlloyType t : visibleUserTypes) {
            // trim label before last slash
            MagicUtil.trimLabelBeforeLastSlash(vizState, t);
        }
        // hide names if there's only one node type visible
        if (1 == visibleUserTypes.size()) {
            vizState.label.put(visibleUserTypes.iterator().next(), "");
        }
    }
}
