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

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;

import javax.swing.BoxLayout;
import javax.swing.Icon;
import javax.swing.JComboBox;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.JSplitPane;
import javax.swing.JTextField;
import javax.swing.SpinnerNumberModel;
import javax.swing.border.EmptyBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.tree.TreePath;

import edu.mit.csail.sdg.alloy4.Listener;
import edu.mit.csail.sdg.alloy4.OurBorder;
import edu.mit.csail.sdg.alloy4.OurCheckbox;
import edu.mit.csail.sdg.alloy4.OurCombobox;
import edu.mit.csail.sdg.alloy4.OurTree;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4graph.DotColor;
import edu.mit.csail.sdg.alloy4graph.DotPalette;
import edu.mit.csail.sdg.alloy4graph.DotShape;
import edu.mit.csail.sdg.alloy4graph.DotStyle;

/**
 * GUI panel for making customization changes.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class VizCustomizationPanel extends JPanel {

    /** This ensures the class can be serialized reliably. */
    private static final long   serialVersionUID = 0;

    /**
     * The TREE NODE representing the root of the customization panel.
     */
    private static final Object ROOT             = new Object();

    /** The TREE NODE representing the GENERAL OPTIONS panel. */
    private static final Object GENERAL          = new Object();

    /** The TREE NODE representing the GENERAL NODES panel. */
    private static final Object NODES            = new Object();

    /** The TREE NODE representing the GENERAL EDGES panel. */
    private static final Object EDGES            = new Object();

    /**
     * This is the VizState object that this customization panel will customize.
     */
    private final VizState      vizState;

    /**
     * This is the background color for the upper-half of the customization panel.
     */
    private static final Color  wcolor           = new Color(0.9f, 0.9f, 0.9f);

    /** This is the upper-half of the customization panel. */
    private final JPanel        zoomPane;

    /**
     * The JSplitPane separating this customization panel with the main graph panel.
     */
    private final JSplitPane    divider;

    /**
     * If it's an instance of AlloyElement, that means it's the latest selected
     * type/set/relation. If it's GENERAL, NODES, or EDGES, that means the latest
     * selected panel is the General Graph Settings, Default Type+Set, or Default
     * Relation panels respectively. All else, that means the zoom panel is empty.
     */
    private Object              lastElement      = null;

    // =============================================================================================================//

    /**
     * Constructs a customization panel.
     *
     * @param divider - the JSplitPane separating the left-customization-half with
     *            the right-graph-half
     * @param vizState - the VizState object that will be customized by this
     *            customization panel
     */
    public VizCustomizationPanel(JSplitPane divider, VizState vizState) {
        this.divider = divider;
        this.vizState = vizState;
        setBorder(null);
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        zoomPane = new JPanel();
        zoomPane.setBorder(new OurBorder(false, false, true, false));
        zoomPane.setLayout(new BoxLayout(zoomPane, BoxLayout.Y_AXIS));
        zoomPane.setAlignmentX(0f);
        zoomPane.setBackground(wcolor);
        remakeAll();
    }

    // =============================================================================================================//

    /**
     * This method selects a particular treenode and shows the details of a
     * particular Type/Set/Relation.
     * <p>
     * If x is an instance of AlloyElement, that means it's the latest selected
     * type/set/relation. If x is GENERAL, NODES, or EDGES, that means the latest
     * selected panel is the General Graph Settings, Default Type+Set, or Default
     * Relation panels respectively.
     */
    private void zoom(Object x) {
        lastElement = x;
        zoomPane.removeAll();
        if (x instanceof AlloyNodeElement)
            makeNodeOptionsPanel(zoomPane, (AlloyNodeElement) x);
        else if (x instanceof AlloyRelation)
            makeEdgeOptionsPanel(zoomPane, (AlloyRelation) x);
        else if (x == GENERAL)
            createGeneralWidget(zoomPane);
        else if (x == NODES)
            createDefaultNodeWidget(zoomPane);
        else if (x == EDGES)
            createDefaultEdgeWidget(zoomPane);
        else {
            // The following 2 lines make sure the panel doesn't get too small
            // on Mac
            zoomPane.add(OurUtil.makeH(wcolor, new JLabel(" "), (Object) null));
            zoomPane.add(OurUtil.makeH(new Dimension(250, 200), wcolor, (Object) null));
        }
        Dimension dim = zoomPane.getPreferredSize();
        if (divider != null && divider.getDividerLocation() < dim.width)
            divider.setDividerLocation(dim.width);
        if (divider != null && divider.getDividerLocation() > dim.width)
            dim.width = divider.getDividerLocation();
        dim.height = 150;
        zoomPane.setPreferredSize(dim);
        dim.width = 450;
        zoomPane.setMinimumSize(dim);
        zoomPane.repaint();
        validate();
    }

    // =============================================================================================================//

    /**
     * Regenerate all the customization widgets based on the latest settings.
     */
    public void remakeAll() {
        // Make the tree
        final OurTree tree = new OurTree(12) {

            private static final long serialVersionUID = 0;
            private final AlloyModel  old              = vizState.getOriginalModel(),
                            now = vizState.getCurrentModel();
            private final boolean     hidePrivate      = vizState.hidePrivate(), hideMeta = vizState.hideMeta();
            {
                do_start();
                setRootVisible(false);
                setShowsRootHandles(false);
                listeners.add(new Listener() {

                    @Override
                    public Object do_action(Object sender, Event event) {
                        return null;
                    }

                    @Override
                    public Object do_action(Object sender, Event event, Object arg) {
                        zoom(arg);
                        return null;
                    }
                });
            }

            @Override
            public String convertValueToText(Object value, boolean sel, boolean expand, boolean leaf, int i, boolean focus) {
                if (value == GENERAL)
                    return "<html><b>general graph settings</b></html>";
                if (value == NODES)
                    return "<html><b>types and sets</b></html>";
                if (value == EDGES)
                    return "<html><b>relations</b></html>";
                if (value instanceof AlloyType) {
                    AlloyType x = (AlloyType) value;
                    if (vizState.getCurrentModel().hasType(x))
                        return "<html><b>sig</b> " + typename(x) + "</html>";
                    return "<html><b>sig</b> " + typename(x) + " <font color=\"#808080\">(projected)</font></html>";
                }
                if (value instanceof AlloySet)
                    return "<html><b>set</b> " + ((AlloySet) value).getName() + "</html>";
                if (value instanceof AlloyRelation)
                    return value.toString();
                else
                    return "";
            }

            @Override
            public List< ? > do_ask(Object parent) {
                ArrayList<Object> ans = new ArrayList<Object>();
                if (parent == ROOT) {
                    ans.add(GENERAL);
                    ans.add(NODES);
                    ans.add(EDGES);
                } else if (parent == NODES) {
                    ans.add(AlloyType.UNIV);
                } else if (parent == EDGES) {
                    for (AlloyRelation rel : vizState.getCurrentModel().getRelations())
                        if (!(hidePrivate && rel.isPrivate) && !(hideMeta && rel.isMeta))
                            ans.add(rel);
                } else if (parent instanceof AlloyType) {
                    AlloyType type = (AlloyType) parent;
                    for (AlloySet s : now.getSets())
                        if (!(hidePrivate && s.isPrivate) && !(hideMeta && s.isMeta) && s.getType().equals(type))
                            ans.add(s);
                    if (!type.isEnum)
                        for (AlloyType t : old.getDirectSubTypes(type))
                            if (!(hidePrivate && t.isPrivate) && !(hideMeta && t.isMeta))
                                if (now.hasType(t) || vizState.canProject(t))
                                    ans.add(t);
                }
                return ans;
            }

            @Override
            public boolean do_isDouble(Object object) {
                return object == NODES || object == EDGES;
            }

            @Override
            public Object do_root() {
                return ROOT;
            }
        };
        // Pre-expand the entire tree.
        TreePath last = null;
        for (int i = 0; i < tree.getRowCount(); i++) {
            tree.expandRow(i);
            if (lastElement != null && last == null) {
                last = tree.getPathForRow(i);
                if (lastElement != last.getLastPathComponent())
                    last = null;
            }
        }
        // Show the current element if found, else show the GENERAL OPTIONS
        if (last != null) {
            zoom(lastElement);
        } else {
            last = tree.getPathForRow(0);
            zoom(GENERAL);
        }
        tree.scrollPathToVisible(last);
        tree.setSelectionPath(last);
        JScrollPane scroll = OurUtil.scrollpane(tree, Color.BLACK, Color.WHITE, new OurBorder(false, false, false, Util.onMac()));
        scroll.setAlignmentX(0f);
        scroll.getVerticalScrollBar().setUnitIncrement(50);
        removeAll();
        add(zoomPane);
        add(scroll);
        validate();
    }

    // =============================================================================================================//

    /**
     * Generates the node settings widgets for the given type or set, and add them
     * to "parent".
     */
    private void makeNodeOptionsPanel(final JPanel answer, final AlloyNodeElement elt) {
        final boolean enabled = !(elt instanceof AlloyType) || (vizState.getCurrentModel().hasType((AlloyType) elt));
        answer.add(makelabel((elt instanceof AlloyType) ? (" " + typename((AlloyType) elt)) : (" " + elt)));
        final JTextField labelText = OurUtil.textfield(vizState.label.get(elt), 10);
        labelText.setMaximumSize(new Dimension(100, 25));
        labelText.addKeyListener(new KeyAdapter() {

            @Override
            public final void keyReleased(KeyEvent e) {
                vizState.label.put(elt, labelText.getText());
            }
        });
        labelText.addActionListener(new ActionListener() {

            @Override
            public final void actionPerformed(ActionEvent e) {
                vizState.label.put(elt, labelText.getText());
            }
        });
        labelText.addFocusListener(new FocusAdapter() {

            @Override
            public void focusLost(FocusEvent e) {
                vizState.label.put(elt, labelText.getText());
            }
        });
        final AlloyModel model = vizState.getCurrentModel();
        final AlloyNodeElement elt2;
        if (elt instanceof AlloyType)
            elt2 = model.getSuperType((AlloyType) elt);
        else if (elt instanceof AlloySet)
            elt2 = ((AlloySet) elt).getType();
        else
            elt2 = null;
        JComboBox color = new OurCombobox(true, DotColor.valuesWithout(DotColor.MAGIC), 100, 35, vizState.nodeColor.get(elt)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                if (value == null)
                    return "Inherit";
                else
                    return ((DotColor) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                if (value == null)
                    value = vizState.nodeColor.resolve(elt2);
                return value == null ? null : ((DotColor) value).getIcon(vizState.getNodePalette());
            }

            @Override
            public void do_changed(Object value) {
                vizState.nodeColor.put(elt, (DotColor) value);
            }
        };
        JComboBox shape = new OurCombobox(true, DotShape.values(), 125, 35, vizState.shape.get(elt)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                if (value == null)
                    return "Inherit";
                else
                    return ((DotShape) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                if (value == null)
                    value = vizState.shape.resolve(elt2);
                return value == null ? null : ((DotShape) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.shape.put(elt, (DotShape) value);
            }
        };
        JComboBox style = new OurCombobox(true, DotStyle.values(), 95, 35, vizState.nodeStyle.get(elt)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                if (value == null)
                    return "Inherit";
                else
                    return ((DotStyle) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                if (value == null)
                    value = vizState.nodeStyle.resolve(elt2);
                return value == null ? null : ((DotStyle) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.nodeStyle.put(elt, (DotStyle) value);
            }
        };
        //
        answer.add(OurUtil.makeH(10, labelText, wcolor, color, style, shape, 2, null));
        if (elt instanceof AlloyType) {
            JPanel vis = vizState.nodeVisible.pick(elt, "Show", "Display members as nodes");
            JPanel con = vizState.hideUnconnected.pick(elt, "Hide unconnected nodes", "Hide nodes without arcs");
            JPanel num = vizState.number.pick(elt, "Number nodes", "Attach atom number to node label as suffix");
            JPanel proj = null;
            if (vizState.canProject((AlloyType) elt))
                proj = new OurCheckbox("Project over this sig", "Click here to " + (enabled ? "" : "un") + "project over this signature", enabled ? OurCheckbox.ALL_OFF : OurCheckbox.ALL_ON) {

                    private static final long serialVersionUID = 0;

                    @Override
                    public Icon do_action() {
                        if (enabled)
                            projectAlloyType((AlloyType) elt);
                        else
                            deprojectAlloyType((AlloyType) elt);
                        lastElement = elt;
                        return enabled ? ALL_ON : ALL_OFF;
                    }
                };
            labelText.setEnabled(enabled && !vizState.useOriginalName());
            color.setEnabled(enabled);
            shape.setEnabled(enabled);
            style.setEnabled(enabled);
            vis.setEnabled(enabled);
            con.setEnabled(enabled);
            num.setEnabled(enabled && !vizState.useOriginalName());
            JPanel a = OurUtil.makeVR(wcolor, vis, num), b;
            if (proj != null)
                b = OurUtil.makeVR(wcolor, con, proj);
            else
                b = OurUtil.makeVR(wcolor, con);
            answer.add(OurUtil.makeHT(wcolor, 15, a, 15, b, 2, null));
        } else {
            JPanel vis = vizState.nodeVisible.pick(elt, "Show", "Include members of set as nodes");
            JPanel attr = vizState.showAsAttr.pick(elt, "Show in relation attributes", "Show set membership in relation attributes");
            JPanel lab = vizState.showAsLabel.pick(elt, "Show as labels", "Show membership in set by labeling nodes");
            JPanel con = vizState.hideUnconnected.pick(elt, "Hide unconnected nodes", "Hide nodes without arcs");
            JPanel a = OurUtil.makeVR(wcolor, vis, lab), b = OurUtil.makeVR(wcolor, con, attr);
            answer.add(OurUtil.makeHT(wcolor, 15, a, 15, b, 2, null));
        }
    }

    // =============================================================================================================//

    /**
     * Generates the edge settings widgets for the given relation, and add them to
     * "parent".
     */
    private void makeEdgeOptionsPanel(final JPanel parent, final AlloyRelation rel) {
        final JTextField labelText = OurUtil.textfield(vizState.label.get(rel), 10);
        labelText.setMaximumSize(new Dimension(100, 25));
        labelText.addKeyListener(new KeyAdapter() {

            @Override
            public void keyReleased(KeyEvent e) {
                vizState.label.put(rel, labelText.getText());
            }
        });
        labelText.addActionListener(new ActionListener() {

            @Override
            public final void actionPerformed(ActionEvent e) {
                vizState.label.put(rel, labelText.getText());
            }
        });
        labelText.addFocusListener(new FocusAdapter() {

            @Override
            public void focusLost(FocusEvent e) {
                vizState.label.put(rel, labelText.getText());
            }
        });
        final JLabel weightLabel = OurUtil.label("Weight:");
        final JSpinner weightSpinner = new JSpinner(new SpinnerNumberModel(vizState.weight.get(rel), 0, 999, 1));
        weightSpinner.setMaximumSize(weightSpinner.getPreferredSize());
        weightSpinner.setToolTipText("A higher weight will cause the edge to be shorter and straighter.");
        weightSpinner.addKeyListener(new KeyAdapter() {

            @Override
            public void keyReleased(KeyEvent e) {
                vizState.weight.put(rel, (Integer) (weightSpinner.getValue()));
            }
        });
        weightSpinner.addMouseListener(new MouseAdapter() {

            @Override
            public void mouseClicked(MouseEvent e) {
                vizState.weight.put(rel, (Integer) (weightSpinner.getValue()));
            }

            @Override
            public void mousePressed(MouseEvent e) {
                vizState.weight.put(rel, (Integer) (weightSpinner.getValue()));
            }

            @Override
            public void mouseReleased(MouseEvent e) {
                vizState.weight.put(rel, (Integer) (weightSpinner.getValue()));
            }
        });
        weightSpinner.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                vizState.weight.put(rel, (Integer) (weightSpinner.getValue()));
            }
        });
        JPanel weightPanel = OurUtil.makeH(weightLabel, 5, weightSpinner);
        weightPanel.setBorder(new EmptyBorder(5, 5, 5, 5));
        weightPanel.setAlignmentY(0.5f);
        weightPanel.setToolTipText("A higher weight will cause the edge to be shorter and straighter.");
        OurCombobox color = new OurCombobox(true, DotColor.valuesWithout(DotColor.WHITE), 110, 35, vizState.edgeColor.get(rel)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return value == null ? "Inherit" : ((DotColor) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                if (value == null)
                    value = vizState.edgeColor.get(null);
                return value == null ? null : ((DotColor) value).getIcon(vizState.getEdgePalette());
            }

            @Override
            public void do_changed(Object value) {
                vizState.edgeColor.put(rel, (DotColor) value);
            }
        };
        OurCombobox style = new OurCombobox(true, DotStyle.values(), 105, 35, vizState.edgeStyle.get(rel)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return value == null ? "Inherit" : ((DotStyle) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                if (value == null)
                    value = vizState.edgeStyle.get(null);
                return value == null ? null : ((DotStyle) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.edgeStyle.put(rel, (DotStyle) value);
            }
        };
        JPanel visible = vizState.edgeVisible.pick(rel, "Show as arcs", "Show relation as arcs");
        JPanel attr = vizState.attribute.pick(rel, "Show as attribute", "Additionally display this relation as an attribute on the nodes' labels");
        JPanel back = vizState.layoutBack.pick(rel, "Layout backwards", "Layout graph as if arcs were reversed");
        JPanel merge = vizState.mergeArrows.pick(rel, "Merge arrows", "Merge opposing arrows between the same nodes as one bidirectional arrow");
        JPanel constraint = vizState.constraint.pick(rel, "Influence layout", "Whether this edge influences the graph layout");
        JPanel panel1 = OurUtil.makeVR(wcolor, visible, attr, constraint);
        JPanel panel2 = OurUtil.makeVR(wcolor, back, merge);
        parent.add(makelabel("<html>&nbsp;" + Util.encode(rel.toString()) + "</html>"));
        parent.add(OurUtil.makeH(10, labelText, wcolor, 5, color, 5, style, 3, weightPanel, 2, null));
        parent.add(OurUtil.makeHT(wcolor, 10, panel1, 15, panel2, 2, null));
    }

    // =============================================================================================================//

    /**
     * Generates the "general graph settings" widgets, and add them to "parent".
     */
    private void createGeneralWidget(JPanel parent) {
        final List<Integer> fontSizes = Util.asList(9, 10, 11, 12, 14, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 54, 60, 66, 72);
        JLabel nLabel = OurUtil.label("Node Color Palette:");
        JLabel eLabel = OurUtil.label("Edge Color Palette:");
        JLabel aLabel = OurUtil.label("Use original atom names:");
        JLabel pLabel = OurUtil.label("Hide private sigs/relations:");
        JLabel mLabel = OurUtil.label("Hide meta sigs/relations:");
        JLabel fLabel = OurUtil.label("Font Size:");
        JComboBox fontSize = new OurCombobox(false, fontSizes.toArray(), 60, 32, vizState.getFontSize()) {

            private static final long serialVersionUID = 0;

            @Override
            public void do_changed(Object value) {
                if (fontSizes.contains(value))
                    vizState.setFontSize((Integer) value);
            }
        };
        JComboBox nodepal = new OurCombobox(false, DotPalette.values(), 100, 32, vizState.getNodePalette()) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotPalette) value).getDisplayedText();
            }

            @Override
            public void do_changed(Object value) {
                vizState.setNodePalette((DotPalette) value);
            }
        };
        JComboBox edgepal = new OurCombobox(false, DotPalette.values(), 100, 32, vizState.getEdgePalette()) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotPalette) value).getDisplayedText();
            }

            @Override
            public void do_changed(Object value) {
                vizState.setEdgePalette((DotPalette) value);
            }
        };
        JPanel name = new OurCheckbox("", "Whether the visualizer should use the original atom names as-is.", vizState.useOriginalName() ? OurCheckbox.ON : OurCheckbox.OFF) {

            private static final long serialVersionUID = 0;

            @Override
            public Icon do_action() {
                boolean x = vizState.useOriginalName();
                vizState.useOriginalName(!x);
                return (!x ? ON : OFF);
            }
        };
        JPanel priv = new OurCheckbox("", "Whether the visualizer should hide private sigs, sets, and relations by default.", vizState.hidePrivate() ? OurCheckbox.ON : OurCheckbox.OFF) {

            private static final long serialVersionUID = 0;

            @Override
            public Icon do_action() {
                boolean x = vizState.hidePrivate();
                vizState.hidePrivate(!x);
                remakeAll();
                return (!x ? ON : OFF);
            }
        };
        JPanel meta = new OurCheckbox("", "Whether the visualizer should hide meta sigs, sets, and relations by default.", vizState.hideMeta() ? OurCheckbox.ON : OurCheckbox.OFF) {

            private static final long serialVersionUID = 0;

            @Override
            public Icon do_action() {
                boolean x = vizState.hideMeta();
                vizState.hideMeta(!x);
                remakeAll();
                return (!x ? ON : OFF);
            }
        };
        parent.add(makelabel(" General Graph Settings:"));
        parent.add(OurUtil.makeH(wcolor, new Dimension(6, 6)));
        parent.add(OurUtil.makeH(wcolor, 25, nLabel, 5, nodepal, 8, aLabel, 5, name, 2, null));
        parent.add(OurUtil.makeH(wcolor, 25, eLabel, 5, edgepal, 8, fLabel, 5, fontSize, 2, null));
        parent.add(OurUtil.makeH(wcolor, 25, pLabel, 5, priv, 2, null));
        parent.add(OurUtil.makeH(wcolor, 25, mLabel, 5, meta, 2, null));
    }

    // =============================================================================================================//

    /**
     * Generates the "default type and set settings" widgets, and add them to
     * "parent".
     */
    private void createDefaultNodeWidget(JPanel parent) {
        JComboBox color = new OurCombobox(false, DotColor.valuesWithout(DotColor.MAGIC), 110, 35, vizState.nodeColor.get(null)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotColor) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                return ((DotColor) value).getIcon(vizState.getNodePalette());
            }

            @Override
            public void do_changed(Object value) {
                vizState.nodeColor.put(null, (DotColor) value);
            }
        };
        JComboBox shape = new OurCombobox(false, DotShape.values(), 135, 35, vizState.shape.get(null)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotShape) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                return ((DotShape) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.shape.put(null, (DotShape) value);
            }
        };
        JComboBox style = new OurCombobox(false, DotStyle.values(), 110, 35, vizState.nodeStyle.get(null)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotStyle) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                return ((DotStyle) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.nodeStyle.put(null, (DotStyle) value);
            }
        };
        JPanel vis = vizState.nodeVisible.pick("Show", "Show members of type as nodes");
        JPanel hide = vizState.hideUnconnected.pick("Hide unconnected nodes", "Hide nodes without arcs");
        JPanel num = vizState.number.pick("Number nodes", "Attach atom number to node label as suffix");
        JPanel label = vizState.showAsLabel.pick("Show as labels", "Show members as labels");
        JPanel attr = vizState.showAsAttr.pick("Show in relation attributes", "Show set membership of endpoints when relation attributes are enabled");
        parent.add(makelabel(" Default Type and Set Settings:"));
        parent.add(OurUtil.makeH(wcolor, 10, color, 7, style, 7, shape, 2, null));
        JPanel a = OurUtil.makeVL(wcolor, vis, num, label), b = OurUtil.makeVL(wcolor, hide, attr);
        parent.add(OurUtil.makeHT(wcolor, 10, a, 10, b, 2, null));
    }

    // =============================================================================================================//

    /**
     * Generates the "default relation settings" widgets, and add them to "parent".
     */
    private void createDefaultEdgeWidget(JPanel parent) {
        JComboBox colorComboE = new OurCombobox(false, DotColor.valuesWithout(DotColor.WHITE), 110, 35, vizState.edgeColor.get(null)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotColor) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                return ((DotColor) value).getIcon(vizState.getEdgePalette());
            }

            @Override
            public void do_changed(Object value) {
                vizState.edgeColor.put(null, (DotColor) value);
            }
        };
        JComboBox outlineComboE = new OurCombobox(false, DotStyle.values(), 110, 35, vizState.edgeStyle.get(null)) {

            private static final long serialVersionUID = 0;

            @Override
            public String do_getText(Object value) {
                return ((DotStyle) value).getDisplayedText();
            }

            @Override
            public Icon do_getIcon(Object value) {
                return ((DotStyle) value).getIcon();
            }

            @Override
            public void do_changed(Object value) {
                vizState.edgeStyle.put(null, (DotStyle) value);
            }
        };
        JPanel dispCBE = vizState.edgeVisible.pick("Show as arcs", "Show relations as arcs");
        JPanel mergeCBE = vizState.mergeArrows.pick("Merge arrows", "Merge opposing arrows of the same relation");
        JPanel constraintCBE = vizState.constraint.pick("Influence layout", "Whether this edge influences the graph layout");
        JPanel attrCBE = vizState.attribute.pick("Show as attributes", "Show relations as attributes on nodes");
        JPanel laybackCBE = vizState.layoutBack.pick("Layout backwards", "Layout graph as if arcs were reversed");
        parent.add(makelabel(" Default Relation Settings:"));
        parent.add(OurUtil.makeH(wcolor, 10, colorComboE, 8, outlineComboE, 2, null));
        JPanel a = OurUtil.makeVL(wcolor, dispCBE, attrCBE, constraintCBE, 10),
                        b = OurUtil.makeVL(wcolor, laybackCBE, mergeCBE);
        parent.add(OurUtil.makeHT(wcolor, 10, a, 10, b, 2, null));
    }

    // =============================================================================================================//

    /**
     * Convenient helper method that returns a description of an AlloyType (and what
     * it extends).
     */
    private String typename(AlloyType type) {
        if (type.equals(AlloyType.UNIV))
            return "univ";
        AlloyType sup = vizState.getOriginalModel().getSuperType(type);
        if (sup != null && !sup.equals(AlloyType.UNIV))
            return type.getName() + " extends " + sup.getName();
        return type.getName();
    }

    /** Generates a black JLabel for the given String. */
    private static JLabel makelabel(String label) {
        return OurUtil.label(label, OurUtil.getVizFont().deriveFont(Font.BOLD));
    }

    /** Project over the given type if we are allowed to. */
    private void projectAlloyType(AlloyType type) {
        vizState.project(type);
        remakeAll();
    }

    /**
     * Unproject over the given type if it is currently projected.
     */
    private void deprojectAlloyType(AlloyType type) {
        vizState.deproject(type);
        remakeAll();
    }
}
