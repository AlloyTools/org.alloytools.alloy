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

import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.event.MouseEvent;
import java.util.WeakHashMap;
import java.util.function.Function;

import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JTextPane;
import javax.swing.ToolTipManager;
import javax.swing.text.DefaultHighlighter;

/**
 * Graphical convenience methods for managing and constructing antialias-capable
 * components.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class OurAntiAlias {

    /**
     * This constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private OurAntiAlias() {}

    /** Use anti-alias or not. */
    private static boolean                         antiAlias = Util.onMac() || Util.onWindows();

    /**
     * Stores weak references of all objects that need to be redrawn when anti-alias
     * setting changes.
     */
    private static WeakHashMap<JComponent,Boolean> map       = new WeakHashMap<>();

    /**
     * Changes whether anti-aliasing should be done or not (when changed, we will
     * automatically repaint all affected components).
     */
    public static void enableAntiAlias(boolean enableAntiAlias) {
        if (antiAlias == enableAntiAlias || Util.onMac() || Util.onWindows())
            return;
        antiAlias = enableAntiAlias;
        for (JComponent x : map.keySet())
            if (x != null) {
                x.invalidate();
                x.repaint();
                x.validate();
            }
    }

    /**
     * Constructs an antialias-capable JLabel.
     *
     * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make
     *            OurUtil.make(component, attributes...)}
     */
    public static JLabel label(String label, Object... attributes) {
        JLabel ans = new JLabel(label) {

            static final long serialVersionUID = 0;

            @Override
            public void paint(Graphics gr) {
                if (antiAlias && gr instanceof Graphics2D) {
                    ((Graphics2D) gr).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
                }
                super.paint(gr);
            }
        };
        OurUtil.make(ans, attributes);
        map.put(ans, Boolean.TRUE);
        return ans;
    }

    /**
     * Constructs an antialias-capable JTextPane with a DefaultHighlighter
     * associated with it.
     *
     * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make
     *            OurUtil.make(component, attributes...)}
     */

    public static JTextPane pane(Function<MouseEvent,String> tooltip, Object... attributes) {
        JTextPane ans = new JTextPane() {

            static final long serialVersionUID = 0;

            @Override
            public void paint(Graphics gr) {
                if (antiAlias && gr instanceof Graphics2D) {
                    ((Graphics2D) gr).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
                }
                super.paint(gr);
            }

            @Override
            public String getToolTipText(MouseEvent event) {
                if (tooltip != null) {
                    return tooltip.apply(event);
                }
                return super.getToolTipText(event);
            }

        };
        if (tooltip != null)
            ToolTipManager.sharedInstance().registerComponent(ans);

        OurUtil.make(ans, attributes);
        ans.setHighlighter(new DefaultHighlighter());
        map.put(ans, Boolean.TRUE);
        return ans;
    }
}
