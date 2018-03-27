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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.Icon;
import javax.swing.JComboBox;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.ListCellRenderer;
import javax.swing.border.EmptyBorder;

/**
 * Graphical combobox.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public class OurCombobox extends JComboBox {

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * This caches a preconstructed JLabel that is used for the rendering of each
     * Combo value.
     */
    private static JLabel     jlabel;

    /**
     * Subclass can override this method to provide the custom text for any given
     * value (It should return "" if no text is needed)
     */
    public String do_getText(Object value) {
        return String.valueOf(value);
    }

    /**
     * Subclass can override this method to provide the custom icon for any given
     * value (It should return null if no icon is needed)
     */
    public Icon do_getIcon(Object value) {
        return null;
    }

    /**
     * Subclass can override this method to react upon selection change.
     */
    public void do_changed(Object newValue) {}

    /**
     * This helper method makes a copy of the list, and then optionally prepend null
     * at the beginning of the list.
     */
    private static Vector<Object> do_copy(Object[] list, boolean addNull) {
        Vector<Object> answer = new Vector<Object>(list.length + (addNull ? 1 : 0));
        if (addNull)
            answer.add(null);
        for (int i = 0; i < list.length; i++)
            answer.add(list[i]);
        return answer;
    }

    /**
     * Constructs a new OurCombobox object.
     *
     * @param list - the list of allowed values
     */
    public OurCombobox(Object[] list) {
        this(false, list, 0, 0, null);
    }

    /**
     * Constructs a new OurCombobox object.
     *
     * @param addNull - whether we should prepend null onto the beginning of the
     *            list of allowed values
     * @param list - the list of allowed values
     * @param width - the width to use (if width==0 and height==0, then we ignore
     *            this parameter)
     * @param height - the height to use (if width==0 and height==0, then we ignore
     *            this parameter)
     * @param initialValue - if nonnull it is the initial value to choose in this
     *            combo box
     */
    public OurCombobox(boolean addNull, Object[] list, int width, int height, Object initialValue) {
        super(do_copy(list, addNull));
        setFont(OurUtil.getVizFont());
        setRenderer(new ListCellRenderer() {

            @Override
            public Component getListCellRendererComponent(JList list, Object value, int i, boolean selected, boolean focused) {
                if (jlabel == null)
                    jlabel = OurUtil.label("", Color.BLACK, Color.WHITE, new EmptyBorder(0, 2, 0, 0));
                jlabel.setText(do_getText(value));
                jlabel.setIcon(do_getIcon(value));
                jlabel.setBackground(selected ? list.getSelectionBackground() : list.getBackground());
                jlabel.setForeground(selected ? list.getSelectionForeground() : list.getForeground());
                return jlabel;
            }
        });
        if (width != 0 || height != 0) { // Make some platform-specific
                                        // adjustments which should make the
                                        // combobox look nicer
            if (Util.onWindows() && height > 25)
                height = 25; // Otherwise, the height is too big on Windows
            setPreferredSize(new Dimension(width, height));
            setMaximumSize(new Dimension(width, height));
            if (!Util.onWindows() && !Util.onMac())
                setBorder(new EmptyBorder(4, 3, 4, 0));
        }
        if (initialValue != null) {
            setSelectedItem(initialValue);
        }
        addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                do_changed(getSelectedItem());
            }
        });
    }
}
