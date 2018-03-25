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

import java.awt.BorderLayout;
import java.awt.Color;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.TreeSet;

import javax.swing.Icon;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import edu.mit.csail.sdg.alloy4.ConstSet;
import edu.mit.csail.sdg.alloy4.MailBug;
import edu.mit.csail.sdg.alloy4.OurCheckbox;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4graph.DotColor;
import edu.mit.csail.sdg.alloy4graph.DotPalette;
import edu.mit.csail.sdg.alloy4graph.DotShape;
import edu.mit.csail.sdg.alloy4graph.DotStyle;

/**
 * Mutable; this stores an unprojected model as well as the current theme
 * customization.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class VizState {

    /**
     * Construct a new VizState (with default theme settings) for the given
     * instance; if world!=null, it is the root of the AST.
     */
    public VizState(AlloyInstance originalInstance) {
        this.originalInstance = originalInstance;
        this.currentModel = originalInstance.model;
        resetTheme();
        loadInstance(originalInstance);
    }

    /** Make a copy of an existing VizState object. */
    public VizState(VizState old) {
        originalInstance = old.originalInstance;
        currentModel = old.currentModel;
        projectedTypes = new TreeSet<AlloyType>(old.projectedTypes);
        useOriginalNames = old.useOriginalNames;
        hidePrivate = old.hidePrivate;
        hideMeta = old.hideMeta;
        fontSize = old.fontSize;
        nodePalette = old.nodePalette;
        edgePalette = old.edgePalette;
        nodeColor.putAll(old.nodeColor);
        nodeStyle.putAll(old.nodeStyle);
        nodeVisible.putAll(old.nodeVisible);
        label.putAll(old.label);
        number.putAll(old.number);
        hideUnconnected.putAll(old.hideUnconnected);
        showAsAttr.putAll(old.showAsAttr);
        showAsLabel.putAll(old.showAsLabel);
        shape.putAll(old.shape);
        weight.putAll(old.weight);
        attribute.putAll(old.attribute);
        mergeArrows.putAll(old.mergeArrows);
        constraint.putAll(old.constraint);
        layoutBack.putAll(old.layoutBack);
        edgeColor.putAll(old.edgeColor);
        edgeStyle.putAll(old.edgeStyle);
        edgeVisible.putAll(old.edgeVisible);
        changedSinceLastSave = false;
    }

    /** Clears the current theme. */
    public void resetTheme() {
        currentModel = originalInstance.model;
        projectedTypes.clear();
        useOriginalNames = false;
        hidePrivate = true;
        hideMeta = true;
        fontSize = 12;
        nodePalette = DotPalette.CLASSIC;
        edgePalette = DotPalette.CLASSIC;
        nodeColor.clear();
        nodeColor.put(null, DotColor.WHITE);
        nodeStyle.clear();
        nodeStyle.put(null, DotStyle.SOLID);
        nodeVisible.clear();
        nodeVisible.put(null, true);
        label.clear();
        label.put(null, "");
        number.clear();
        number.put(null, true);
        hideUnconnected.clear();
        hideUnconnected.put(null, false);
        showAsAttr.clear();
        showAsAttr.put(null, false);
        showAsLabel.clear();
        showAsLabel.put(null, true);
        shape.clear();
        shape.put(null, DotShape.ELLIPSE);
        weight.clear();
        weight.put(null, 0);
        attribute.clear();
        attribute.put(null, false);
        mergeArrows.clear();
        mergeArrows.put(null, true);
        constraint.clear();
        constraint.put(null, true);
        layoutBack.clear();
        layoutBack.put(null, false);
        edgeColor.clear();
        edgeColor.put(null, DotColor.MAGIC);
        edgeStyle.clear();
        edgeStyle.put(null, DotStyle.SOLID);
        edgeVisible.clear();
        edgeVisible.put(null, true);
        // Provide some nice defaults for "Int" and "seq/Int" type
        AlloyType sigint = AlloyType.INT;
        label.put(sigint, "");
        number.put(sigint, true);
        hideUnconnected.put(sigint, true);
        AlloyType seqidx = AlloyType.SEQINT;
        label.put(seqidx, "");
        number.put(seqidx, true);
        hideUnconnected.put(seqidx, true);
        // Provide some nice defaults for meta model stuff
        AlloyType set = AlloyType.SET;
        AlloyRelation ext = AlloyRelation.EXTENDS, in = AlloyRelation.IN;
        shape.put(null, DotShape.BOX);
        nodeColor.put(null, DotColor.YELLOW);
        nodeStyle.put(null, DotStyle.SOLID);
        shape.put(set, DotShape.ELLIPSE);
        nodeColor.put(set, DotColor.BLUE);
        label.put(set, "");
        edgeColor.put(ext, DotColor.BLACK);
        weight.put(ext, 100);
        layoutBack.put(ext, true);
        edgeColor.put(in, DotColor.BLACK);
        weight.put(in, 100);
        layoutBack.put(in, true);
        // Done
        cache.clear();
        changedSinceLastSave = false;
    }

    /**
     * Load a new instance into this VizState object (the input argument is treated
     * as a new unprojected instance); if world!=null, it is the root of the AST
     */
    public void loadInstance(AlloyInstance unprojectedInstance) {
        this.originalInstance = unprojectedInstance;
        for (AlloyType t : getProjectedTypes())
            if (!unprojectedInstance.model.hasType(t))
                projectedTypes.remove(t);
        currentModel = StaticProjector.project(unprojectedInstance.model, projectedTypes);
        cache.clear();
    }

    /**
     * Erase the current theme customizations and then load it from a file.
     *
     * @throws IOException - if an error occurred
     */
    public void loadPaletteXML(String filename) throws IOException {
        resetTheme();
        StaticThemeReaderWriter.readAlloy(filename, this);
        cache.clear();
        changedSinceLastSave = false;
    }

    /**
     * Saves the current theme to a file (which will be overwritten if it exists
     * already).
     *
     * @throws IOException - if an error occurred
     */
    public void savePaletteXML(String filename) throws IOException {
        StaticThemeReaderWriter.writeAlloy(filename, this);
        changedSinceLastSave = false;
    }

    /** Caches previously generated graphs. */
    private LinkedHashMap<AlloyProjection,JPanel> cache = new LinkedHashMap<AlloyProjection,JPanel>();

    /**
     * Generate a VizGraphPanel for a given projection choice, using the current
     * settings.
     */
    public JPanel getGraph(AlloyProjection projectionChoice) {
        JPanel ans = cache.get(projectionChoice);
        if (ans != null)
            return ans;
        AlloyInstance inst = originalInstance;
        try {
            ans = StaticGraphMaker.produceGraph(inst, this, projectionChoice);
            cache.put(projectionChoice, ans);
        } catch (Throwable ex) {
            String msg = "An error has occurred: " + ex + "\n\nStackTrace:\n" + MailBug.dump(ex) + "\n";
            JScrollPane scroll = OurUtil.scrollpane(OurUtil.textarea(msg, 0, 0, false, false));
            ans = new JPanel();
            ans.setLayout(new BorderLayout());
            ans.add(scroll, BorderLayout.CENTER);
            ans.setBackground(Color.WHITE);
        }
        ans.setBorder(null);
        return ans;
    }

    /** True if the theme has been modified since last save. */
    private boolean changedSinceLastSave = false;

    /** True if the theme has been modified since last save. */
    public boolean changedSinceLastSave() {
        return changedSinceLastSave;
    }

    /**
     * Sets the "changed since last save" flag, then flush any cached generated
     * graphs.
     */
    private void change() {
        changedSinceLastSave = true;
        cache.clear();
    }

    /**
     * If oldValue is different from newValue, then sets the "changed since last
     * save" flag and flush the cache.
     */
    private void changeIf(Object oldValue, Object newValue) {
        if (oldValue == null) {
            if (newValue == null)
                return;
        } else {
            if (oldValue.equals(newValue))
                return;
        }
        change();
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * If x is an AlloyType, x is not univ, then return its parent (which could be
     * univ); If x is an AlloySet, then return x's type; All else, return null.
     */
    private AlloyType parent(AlloyElement x, AlloyModel model) {
        if (x instanceof AlloySet)
            return ((AlloySet) x).getType();
        if (x instanceof AlloyType)
            return model.getSuperType((AlloyType) x);
        return null;
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The original unprojected instance. */
    private AlloyInstance originalInstance;

    /** Returns the original unprojected model. */
    public AlloyInstance getOriginalInstance() {
        return originalInstance;
    }

    /** Returns the original unprojected model. */
    public AlloyModel getOriginalModel() {
        return originalInstance.model;
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The current (possibly projected) model. */
    private AlloyModel currentModel;

    /** Returns the current (possibly projected) model. */
    public AlloyModel getCurrentModel() {
        return currentModel;
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The set of types we are currently projecting over. */
    private Set<AlloyType> projectedTypes = new TreeSet<AlloyType>();

    /**
     * Gets an unmodifiable copy of the set of types we are currently projecting
     * over.
     */
    public ConstSet<AlloyType> getProjectedTypes() {
        return ConstSet.make(projectedTypes);
    }

    /**
     * Returns true iff the type is not univ, and it is a toplevel type.
     */
    public boolean canProject(final AlloyType type) {
        return isTopLevel(type);
    }

    /**
     * Returns true iff the type is not univ, and it is a toplevel type.
     */
    public boolean isTopLevel(final AlloyType type) {
        return AlloyType.UNIV.equals(originalInstance.model.getSuperType(type));
    }

    /**
     * Adds type to the list of projected types if it's a toplevel type.
     */
    public void project(AlloyType type) {
        if (canProject(type))
            if (projectedTypes.add(type)) {
                currentModel = StaticProjector.project(originalInstance.model, projectedTypes);
                change();
            }
    }

    /**
     * Removes type from the list of projected types if it is currently projected.
     */
    public void deproject(AlloyType type) {
        if (projectedTypes.remove(type)) {
            currentModel = StaticProjector.project(originalInstance.model, projectedTypes);
            change();
        }
    }

    /** Removes every entry from the list of projected types. */
    public void deprojectAll() {
        if (projectedTypes.size() > 0) {
            projectedTypes.clear();
            currentModel = StaticProjector.project(originalInstance.model, projectedTypes);
            change();
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Whether to use the original atom names. */
    private boolean useOriginalNames = false;

    /** Returns whether we will use original atom names. */
    public boolean useOriginalName() {
        return useOriginalNames;
    }

    /** Sets whether we will use original atom names or not. */
    public void useOriginalName(Boolean newValue) {
        if (newValue != null && useOriginalNames != newValue) {
            change();
            useOriginalNames = newValue;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Whether to hide private sigs/fields/relations. */
    private boolean hidePrivate = false;

    /**
     * Returns whether we will hide private sigs/fields/relations.
     */
    public boolean hidePrivate() {
        return hidePrivate;
    }

    /**
     * Sets whether we will hide private sigs/fields/relations.
     */
    public void hidePrivate(Boolean newValue) {
        if (newValue != null && hidePrivate != newValue) {
            change();
            hidePrivate = newValue;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Whether to hide meta sigs/fields/relations. */
    private boolean hideMeta = true;

    /**
     * Returns whether we will hide meta sigs/fields/relations.
     */
    public boolean hideMeta() {
        return hideMeta;
    }

    /** Sets whether we will hide meta sigs/fields/relations. */
    public void hideMeta(Boolean newValue) {
        if (newValue != null && hideMeta != newValue) {
            change();
            hideMeta = newValue;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The graph's font size. */
    private int fontSize = 12;

    /** Returns the font size. */
    public int getFontSize() {
        return fontSize;
    }

    /** Sets the font size. */
    public void setFontSize(int n) {
        if (fontSize != n && fontSize > 0) {
            change();
            fontSize = n;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The default node palette. */
    private DotPalette nodePalette;

    /** Gets the default node palette. */
    public DotPalette getNodePalette() {
        return nodePalette;
    }

    /** Sets the default node palette. */
    public void setNodePalette(DotPalette x) {
        if (nodePalette != x && x != null) {
            change();
            nodePalette = x;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** The default edge palette. */
    private DotPalette edgePalette;

    /** Gets the default edge palette. */
    public DotPalette getEdgePalette() {
        return edgePalette;
    }

    /** Sets the default edge palette. */
    public void setEdgePalette(DotPalette x) {
        if (edgePalette != x && x != null) {
            change();
            edgePalette = x;
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    // An important invariant to maintain: every map here must map null to a
    // nonnull value.
    public final MInt           weight          = new MInt();
    public final MString        label           = new MString();
    public final MMap<DotColor> nodeColor       = new MMap<DotColor>();
    public final MMap<DotColor> edgeColor       = new MMap<DotColor>();
    public final MMap<DotStyle> nodeStyle       = new MMap<DotStyle>();
    public final MMap<DotStyle> edgeStyle       = new MMap<DotStyle>();
    public final MMap<DotShape> shape           = new MMap<DotShape>();
    public final MMap<Boolean>  attribute       = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  mergeArrows     = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  constraint      = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  layoutBack      = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  edgeVisible     = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  nodeVisible     = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  number          = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  hideUnconnected = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  showAsAttr      = new MMap<Boolean>(true, false);
    public final MMap<Boolean>  showAsLabel     = new MMap<Boolean>(true, false);

    public final class MInt {

        private final LinkedHashMap<AlloyElement,Integer> map = new LinkedHashMap<AlloyElement,Integer>();

        private MInt() {}

        private void clear() {
            map.clear();
            change();
        }

        private void putAll(MInt x) {
            map.putAll(x.map);
            change();
        }

        public int get(AlloyElement x) {
            Integer ans = map.get(x);
            if (ans == null)
                return 0;
            else
                return ans;
        }

        public void put(AlloyElement x, Integer v) {
            if (v == null || v < 0)
                v = 0;
            changeIf(map.put(x, v), v);
        }
    }

    public final class MString {

        private final LinkedHashMap<AlloyElement,String> map = new LinkedHashMap<AlloyElement,String>();

        private MString() {}

        private void clear() {
            map.clear();
            change();
        }

        private void putAll(MString x) {
            map.putAll(x.map);
            change();
        }

        public String get(AlloyElement x) {
            String ans = map.get(x);
            if (ans == null)
                ans = x.getName().trim();
            return ans;
        }

        public void put(AlloyElement x, String v) {
            if (x == null && v == null)
                v = "";
            if (x != null && x.getName().equals(v))
                v = null;
            changeIf(map.put(x, v), v);
        }
    }

    public final class MMap<T> {

        private final LinkedHashMap<AlloyElement,T> map = new LinkedHashMap<AlloyElement,T>();
        private final T                             onValue;
        private final T                             offValue;

        private MMap() {
            onValue = null;
            offValue = null;
        }

        private MMap(T on, T off) {
            this.onValue = on;
            this.offValue = off;
        }

        private void clear() {
            map.clear();
            change();
        }

        private void putAll(MMap<T> x) {
            map.putAll(x.map);
            change();
        }

        public T get(AlloyElement obj) {
            return map.get(obj);
        }

        public T resolve(AlloyElement obj) {
            AlloyModel m = currentModel;
            for (AlloyElement x = obj;; x = parent(x, m)) {
                T v = map.get(x);
                if (v != null)
                    return v;
            }
        }

        /**
         * Set the value for the given object; can be "null" to mean "inherit"
         */
        public void put(AlloyElement obj, T value) {
            if (obj == null && value == null)
                return;
            Object old = map.put(obj, value);
            if ((old == null && value != null) || (old != null && !old.equals(value)))
                change();
        }

        OurCheckbox pick(String label, String tooltip) {
            return new OurCheckbox(label, tooltip, (Boolean.TRUE.equals(get(null)) ? OurCheckbox.ON : OurCheckbox.OFF)) {

                private static final long serialVersionUID = 0;

                @Override
                public Icon do_action() {
                    T old = get(null);
                    boolean ans = (old != null && old.equals(onValue));
                    MMap.this.put(null, ans ? offValue : onValue);
                    return ans ? OFF : ON;
                }
            };
        }

        OurCheckbox pick(final AlloyElement obj, final String label, final String tooltip) {
            T a = get(obj), b = resolve(obj);
            Icon icon = a == null ? (Boolean.TRUE.equals(b) ? OurCheckbox.INH_ON : OurCheckbox.INH_OFF) : (Boolean.TRUE.equals(a) ? OurCheckbox.ALL_ON : OurCheckbox.ALL_OFF);
            return new OurCheckbox(label, tooltip, icon) {

                private static final long serialVersionUID = 0;

                @Override
                public Icon do_action() {
                    T a = get(obj);
                    if (a == null)
                        a = onValue;
                    else if (a.equals(onValue))
                        a = offValue;
                    else
                        a = null;
                    MMap.this.put(obj, a);
                    return a == null ? (Boolean.TRUE.equals(resolve(obj)) ? INH_ON : INH_OFF) : (Boolean.TRUE.equals(a) ? ALL_ON : ALL_OFF);
                }
            };
        }
    }

    // Reads the value for that type/set/relation.
    // If x==null, then we guarantee the return value is nonnull
    // If x!=null, then it may return null (which means "inherited")
    // (Note: "label" and "weight" will never return null)

    // Reads the value for that atom based on an existing AlloyInstance; return
    // value is never null.
    public DotColor nodeColor(AlloyAtom a, AlloyInstance i) {
        for (AlloySet s : i.atom2sets(a)) {
            DotColor v = nodeColor.get(s);
            if (v != null)
                return v;
        }
        return nodeColor.resolve(a.getType());
    }

    public DotStyle nodeStyle(AlloyAtom a, AlloyInstance i) {
        for (AlloySet s : i.atom2sets(a)) {
            DotStyle v = nodeStyle.get(s);
            if (v != null)
                return v;
        }
        return nodeStyle.resolve(a.getType());
    }

    public DotShape shape(AlloyAtom a, AlloyInstance i) {
        for (AlloySet s : i.atom2sets(a)) {
            DotShape v = shape.get(s);
            if (v != null)
                return v;
        }
        return shape.resolve(a.getType());
    }

    public boolean nodeVisible(AlloyAtom a, AlloyInstance i) {
        // If it's in 1 or more set, then TRUE if at least one of them is TRUE.
        // If it's in 0 set, then travel up the chain of AlloyType and return
        // the first non-null value.
        if (i.atom2sets(a).size() > 0) {
            for (AlloySet s : i.atom2sets(a))
                if (nodeVisible.resolve(s))
                    return true;
            return false;
        }
        return nodeVisible.resolve(a.getType());
    }
}
