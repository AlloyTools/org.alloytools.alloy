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
import java.awt.Graphics;
import java.awt.Rectangle;
import java.awt.Shape;

import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter;
import javax.swing.text.JTextComponent;

/**
 * Graphica highlighter.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class OurHighlighter implements Highlighter.HighlightPainter {

    /** The color to use when drawing highlights. */
    public final Color color;

    /** Construct a highlighter with the given color. */
    public OurHighlighter(Color color) {
        this.color = color;
    }

    /** This method is called by Swing to draw highlights. */
    @Override
    public void paint(Graphics gr, int start, int end, Shape shape, JTextComponent text) {
        Color old = gr.getColor();
        gr.setColor(color);
        try {
            Rectangle box = shape.getBounds(), a = text.getUI().modelToView(text, start),
                            b = text.getUI().modelToView(text, end);
            if (a.y == b.y) {
                // same line (Note: furthermore, if start==end, then we draw all
                // the way to the right edge)
                Rectangle r = a.union(b);
                gr.fillRect(r.x, r.y, (r.width <= 1 ? (box.x + box.width - r.x) : r.width), r.height);
            } else {
                // Multiple lines; (Note: on first line we'll draw from "start"
                // and extend to rightmost)
                gr.fillRect(a.x, a.y, box.x + box.width - a.x, a.height);
                if (a.y + a.height < b.y)
                    gr.fillRect(box.x, a.y + a.height, box.width, b.y - (a.y + a.height));
                gr.fillRect(box.x, b.y, b.x - box.x, b.height);
            }
        } catch (BadLocationException e) {} // Failure to highlight is not fatal
        gr.setColor(old);
    }
}
