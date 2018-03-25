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

package edu.mit.csail.sdg.alloy4graph;

import static java.awt.BasicStroke.CAP_ROUND;
import static java.awt.BasicStroke.JOIN_ROUND;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.font.FontRenderContext;
import java.awt.font.GlyphVector;
import java.awt.geom.CubicCurve2D;
import java.awt.geom.Rectangle2D;
import java.awt.image.BufferedImage;

import edu.mit.csail.sdg.alloy4.OurPDFWriter;

/**
 * This class abstracts the drawing operations so that we can draw the graph
 * using different frameworks such as Java2D or PDF.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final strictfp class Artist {

    /** The font name. */
    private static final String fontName = "Lucida Grande";

    /** The font size. */
    private static final int    fontSize = 12;

    /** The corresponding Graphics2D object. */
    private Graphics2D          gr;

    /** The corresponding OurPDFWriter. */
    private OurPDFWriter        pdf;

    /**
     * Construct an artist that acts as a wrapper around the given Graphics2D
     * object.
     */
    public Artist(Graphics2D graphics2D) {
        this.gr = graphics2D;
        this.pdf = null;
    }

    /**
     * Construct an artist that acts as a wrapper around the given OurPDFWriter
     * object.
     */
    public Artist(OurPDFWriter pdfWriter) {
        this.gr = null;
        this.pdf = pdfWriter;
    }

    /** Shifts the coordinate space by the given amount. */
    public void translate(int x, int y) {
        if (gr != null)
            gr.translate(x, y);
        else
            pdf.shiftCoordinateSpace(x, y);
    }

    /** Draws a circle of the given radius, centered at (0,0) */
    public void drawCircle(int radius) {
        if (gr != null)
            gr.drawArc(-radius, -radius, radius * 2, radius * 2, 0, 360);
        else
            pdf.drawCircle(radius, false);
    }

    /** Fills a circle of the given radius, centered at (0,0) */
    public void fillCircle(int radius) {
        if (gr != null)
            gr.fillArc(-radius, -radius, radius * 2, radius * 2, 0, 360);
        else
            pdf.drawCircle(radius, true);
    }

    /** Draws a line from (x1,y1) to (x2,y2) */
    public void drawLine(int x1, int y1, int x2, int y2) {
        if (gr != null)
            gr.drawLine(x1, y1, x2, y2);
        else
            pdf.drawLine(x1, y1, x2, y2);
    }

    /** Changes the current color. */
    public void setColor(Color color) {
        if (gr != null)
            gr.setColor(color);
        else
            pdf.setColor(color);
    }

    /** Returns true if left<=x<=right or right<=x<=left. */
    private static boolean in(double left, double x, double right) {
        return (left <= x && x <= right) || (right <= x && x <= left);
    }

    /**
     * Draws the given curve smoothly (assuming the curve is monotonic vertically)
     */
    public void drawSmoothly(Curve curve) {
        final int smooth = 15;
        double cx = 0, cy = 0, slope;
        for (int n = curve.list.size(), i = 0; i < n; i++) {
            CubicCurve2D.Double c = new CubicCurve2D.Double(), c2 = (i + 1 < n) ? curve.list.get(i + 1) : null;
            c.setCurve(curve.list.get(i));
            if (i > 0) {
                c.ctrlx1 = cx;
                c.ctrly1 = cy;
            }
            if (c2 == null) {
                draw(c, false);
                return;
            }
            if ((c.x1 < c.x2 && c2.x2 < c2.x1) || (c.x1 > c.x2 && c2.x2 > c2.x1))
                slope = 0;
            else
                slope = (c2.x2 - c.x1) / (c2.y2 - c.y1);
            double tmp = c.y2 - smooth, tmpx = c.x2 - smooth * slope;
            if (tmp > c.ctrly1 && tmp < c.y2 && in(c.x1, tmpx, c.x2)) {
                c.ctrly2 = tmp;
                c.ctrlx2 = tmpx;
            }
            double tmp2 = c2.y1 + smooth, tmp2x = c2.x1 + smooth * slope;
            if (tmp2 > c2.y1 && tmp2 < c2.ctrly2 && in(c2.x1, tmp2x, c2.x2)) {
                cy = tmp2;
                cx = tmp2x;
            } else {
                cy = c2.ctrly1;
                cx = c2.ctrlx1;
            }
            draw(c, false);
        }
    }

    /** Draws the given curve. */
    public void draw(Curve curve) {
        for (CubicCurve2D.Double c : curve.list)
            draw(c, false);
    }

    /** Draws the outline of the given shape. */
    public void draw(Shape shape, boolean fillOrNot) {
        if (gr == null)
            pdf.drawShape(shape, fillOrNot);
        else if (fillOrNot)
            gr.fill(shape);
        else
            gr.draw(shape);
    }

    /** The pattern for dotted line. */
    private static float[] dot    = new float[] {
                                                 1f, 3f
    };

    /** The pattern for dashed line. */
    private static float[] dashed = new float[] {
                                                 6f, 3f
    };

    /**
     * Modifies the given Graphics2D object to use the line style representing by
     * this object.
     * <p>
     * NOTE: as a special guarantee, if gr2d==null, then this method returns
     * immediately without doing anything.
     * <p>
     * NOTE: just like the typical AWT and Swing methods, this method can be called
     * only by the AWT event dispatching thread.
     */
    public void set(DotStyle style, double scale) {
        if (gr != null) {
            BasicStroke bs;
            switch (style) {
                case BOLD :
                    bs = new BasicStroke(scale > 1 ? (float) (2.6d / scale) : 2.6f);
                    break;
                case DOTTED :
                    bs = new BasicStroke(scale > 1 ? (float) (1.3d / scale) : 1.3f, CAP_ROUND, JOIN_ROUND, 15f, dot, 0f);
                    break;
                case DASHED :
                    bs = new BasicStroke(scale > 1 ? (float) (1.3d / scale) : 1.3f, CAP_ROUND, JOIN_ROUND, 15f, dashed, 5f);
                    break;
                default :
                    bs = new BasicStroke(scale > 1 ? (float) (1.3d / scale) : 1.3f);
            }
            gr.setStroke(bs);
            return;
        }
        switch (style) {
            case BOLD :
                pdf.setBoldLine();
                return;
            case DOTTED :
                pdf.setDottedLine();
                return;
            case DASHED :
                pdf.setDashedLine();
                return;
            default :
                pdf.setNormalLine();
                return;
        }
    }

    /** Saves the current font boldness. */
    private boolean fontBoldness = false;

    /** Changes the current font. */
    public void setFont(boolean fontBoldness) {
        calc();
        if (gr != null)
            gr.setFont(fontBoldness ? cachedBoldFont : cachedPlainFont);
        else
            this.fontBoldness = fontBoldness;
    }

    /** Draws the given string at (x,y) */
    public void drawString(String text, int x, int y) {
        if (text.length() == 0)
            return;
        if (gr != null) {
            gr.drawString(text, x, y);
            return;
        }
        calc();
        Font font = (fontBoldness ? cachedBoldFont : cachedPlainFont);
        GlyphVector gv = font.createGlyphVector(new FontRenderContext(null, false, false), text);
        translate(x, y);
        draw(gv.getOutline(), true);
        translate(-x, -y);
    }

    /**
     * If nonnull, it caches a Graphics2D object for calculating string bounds.
     */
    private static Graphics2D  cachedGraphics     = null;

    /**
     * If nonnull, it caches a FontMetrics object associated with the nonbold font.
     */
    private static FontMetrics cachedPlainMetrics = null;

    /**
     * If nonnull, it caches a FontMetrics object associated with the bold font.
     */
    private static FontMetrics cachedBoldMetrics  = null;

    /** If nonnull, it caches the nonbold Font. */
    private static Font        cachedPlainFont    = null;

    /** If nonnull, it caches the bold Font. */
    private static Font        cachedBoldFont     = null;

    /**
     * If nonnegative, it caches the maximum ascent of the font.
     */
    private static int         cachedMaxAscent    = -1;

    /**
     * If nonnegative, it caches the maximum descent of the font.
     */
    private static int         cachedMaxDescent   = -1;

    /**
     * Allocates the nonbold and bold fonts, then calculates the max ascent and
     * descent.
     */
    private static void calc() {
        if (cachedMaxDescent >= 0)
            return; // already done
        BufferedImage image = new BufferedImage(1, 1, BufferedImage.TYPE_INT_RGB);
        cachedGraphics = (Graphics2D) (image.getGraphics());
        cachedPlainMetrics = cachedGraphics.getFontMetrics(cachedPlainFont = new Font(fontName, Font.PLAIN, fontSize));
        cachedBoldMetrics = cachedGraphics.getFontMetrics(cachedBoldFont = new Font(fontName, Font.BOLD, fontSize));
        cachedGraphics.setFont(cachedPlainFont);
        cachedMaxAscent = cachedPlainMetrics.getMaxAscent();
        cachedMaxDescent = cachedPlainMetrics.getMaxDescent();
    }

    /**
     * Returns the max ascent when drawing text using the given font size and font
     * boldness settings.
     */
    public static int getMaxAscent() {
        calc();
        return cachedMaxAscent;
    }

    /**
     * Returns the sum of the max ascent and max descent when drawing text using the
     * given font size and font boldness settings.
     */
    public static int getMaxAscentAndDescent() {
        calc();
        return cachedMaxAscent + cachedMaxDescent;
    }

    /**
     * Returns the bounding box when drawing the given string using the given font
     * size and font boldness settings.
     */
    public static Rectangle2D getBounds(boolean fontBoldness, String string) {
        calc();
        return (fontBoldness ? cachedBoldMetrics : cachedPlainMetrics).getStringBounds(string, cachedGraphics);
    }
}
