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

package edu.mit.csail.sdg.alloy4;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.util.IdentityHashMap;
import java.util.List;

import javax.swing.JLabel;
import javax.swing.JTree;
import javax.swing.SwingConstants;
import javax.swing.UIManager;
import javax.swing.border.EmptyBorder;
import javax.swing.event.TreeModelListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

/**
 * Graphical tree.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public abstract class OurTree extends JTree {

    /**
     * The current list of listeners; whenever a node X is selected we'll send
     * (Event.CLICK, X) to each listener.
     */
    public final Listeners listeners = new Listeners();

    /**
     * Custom TreeCellRenderer to print the tree nodes better. (The idea of using
     * JLabel is inspired by DefaultTreeCellRenderer)
     */
    private final class OurTreeRenderer extends JLabel implements TreeCellRenderer {

        /** This ensures the class can be serialized reliably. */
        private static final long serialVersionUID = 0;
        /** This stores the height of one line of text. */
        private int               height;
        /**
         * If preferredHeight > 0, then preferredWidth is the desired width for the
         * current object being drawn.
         */
        private int               preferredWidth   = 0;
        /**
         * If preferredHeight > 0, then preferredHeight is the desired height for the
         * current object being drawn.
         */
        private int               preferredHeight  = 0;
        /** Whether the current object is selected or not. */
        private boolean           isSelected;
        /** Whether the current object is focused or not. */
        private boolean           isFocused;

        /** Constructs this renderer. */
        public OurTreeRenderer(int fontSize) {
            super("Anything"); // This ensures that the height is calculated
                              // properly
            setFont(OurUtil.getVizFont().deriveFont((float) fontSize));
            setVerticalAlignment(SwingConstants.BOTTOM);
            setBorder(new EmptyBorder(0, 3, 0, 3));
            setText("Anything"); // So that we can derive the height
            height = super.getPreferredSize().height;
        }

        /**
         * This method is called by Swing to return an object to be drawn.
         */
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean isSelected, boolean expanded, boolean isLeaf, int row, boolean isFocused) {
            String string = tree.convertValueToText(value, isSelected, expanded, isLeaf, row, isFocused);
            this.isFocused = isFocused;
            this.isSelected = isSelected;
            setText(string);
            setForeground(UIManager.getColor(isSelected ? "Tree.selectionForeground" : "Tree.textForeground"));
            preferredHeight = 0; // By default, don't override width/height
            if (do_isDouble(value)) {
                Dimension d = super.getPreferredSize();
                preferredWidth = d.width + 3;
                preferredHeight = d.height * 2;
            }
            return this;
        }

        /**
         * We override the getPreferredSize() method to return a custom size if
         * do_isDouble() returns true for that value.
         */
        @Override
        public Dimension getPreferredSize() {
            if (preferredHeight > 0)
                return new Dimension(preferredWidth, preferredHeight);
            Dimension d = super.getPreferredSize();
            return new Dimension(d.width + 3, d.height);
        }

        /**
         * We override the paint() method to avoid drawing the box around the "extra
         * space" (if height is double height)
         */
        @Override
        public void paint(Graphics g) {
            int w = getWidth(), h = getHeight(), y = h - height;
            Color background = isSelected ? UIManager.getColor("Tree.selectionBackground") : Color.WHITE;
            Color border = isFocused ? UIManager.getColor("Tree.selectionBorderColor") : null;
            if (background != null) {
                g.setColor(background);
                g.fillRect(0, y, w, h - y);
            }
            if (border != null && isSelected) {
                g.setColor(border);
                g.drawRect(0, y, w - 1, h - 1 - y);
            }
            super.paint(g);
        }
    }

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Subclass should implement this method to return the root of the tree.
     */
    public abstract Object do_root();

    /**
     * Subclass should implement this method to return the list of children nodes
     * given a particular node.
     */
    public abstract List< ? > do_ask(Object parent);

    /**
     * Subclass should override this method to return whether a given item should be
     * double-height or not (default = no).
     */
    protected boolean do_isDouble(Object object) {
        return false;
    }

    /**
     * Subclass should call this when all fields are initialized; we won't call
     * do_root() and do_ask() until subclass calls this.
     */
    protected final void do_start() {
        // Create a custom TreeModel that calls do_root() and do_ask() whenever
        // the tree needs expansion
        setModel(new TreeModel() {

            // Cache the parent->child list so that we always get the exact same
            // OBJECT REFERENCE when navigating the tree
            private final IdentityHashMap<Object,List< ? >> map = new IdentityHashMap<Object,List< ? >>();

            @Override
            public Object getChild(Object parent, int index) {
                List< ? > ans = map.get(parent);
                if (ans == null) {
                    ans = do_ask(parent);
                    map.put(parent, ans);
                }
                return (index >= 0 && index < ans.size()) ? ans.get(index) : null;
            }

            @Override
            public int getIndexOfChild(Object parent, Object child) {
                getChild(parent, 0);
                List< ? > ans = map.get(parent);
                for (int i = 0;; i++)
                    if (i == ans.size())
                        return -1;
                    else if (ans.get(i) == child)
                        return i;
            }

            @Override
            public Object getRoot() {
                return do_root();
            }

            @Override
            public int getChildCount(Object node) {
                getChild(node, 0);
                return map.get(node).size();
            }

            @Override
            public boolean isLeaf(Object node) {
                getChild(node, 0);
                return map.get(node).isEmpty();
            }

            @Override
            public void valueForPathChanged(TreePath path, Object newValue) {}

            @Override
            public void addTreeModelListener(TreeModelListener l) {}

            @Override
            public void removeTreeModelListener(TreeModelListener l) {}
        });
    }

    /**
     * This method is called by Swing to figure out what text should be displayed
     * for each node in the tree.
     */
    @Override
    public abstract String convertValueToText(Object v, boolean select, boolean expand, boolean leaf, int i, boolean focus);

    /** Construct a Tree object with the given font size. */
    public OurTree(int fontSize) {
        Font font = OurUtil.getVizFont().deriveFont((float) fontSize);
        OurTreeRenderer renderer = new OurTreeRenderer(fontSize);
        renderer.setFont(font);
        renderer.invalidate();
        renderer.validate();
        setRowHeight(0); // To allow variable row height on Mac OS X
        setCellRenderer(renderer);
        setFont(font);
        setBorder(new EmptyBorder(8, 8, 2, 2));
        getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        putClientProperty("JTree.lineStyle", "Angled");
        setRootVisible(true);
        setForeground(Color.BLACK);
        setBackground(Color.WHITE);
        setOpaque(true);
        addTreeSelectionListener(new TreeSelectionListener() {

            @Override
            public void valueChanged(TreeSelectionEvent e) {
                TreePath path = OurTree.this.getSelectionPath();
                if (path != null)
                    OurTree.this.listeners.fire(OurTree.this, Listener.Event.CLICK, path.getLastPathComponent());
            }
        });
    }
}
